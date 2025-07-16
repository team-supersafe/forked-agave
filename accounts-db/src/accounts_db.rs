//! Persistent accounts are stored at this path location:
//!  `<path>/<pid>/data/`
//!
//! The persistent store would allow for this mode of operation:
//!  - Concurrent single thread append with many concurrent readers.
//!
//! The underlying memory is memory mapped to a file. The accounts would be
//! stored across multiple files and the mappings of file and offset of a
//! particular account would be stored in a shared index. This will allow for
//! concurrent commits without blocking reads, which will sequentially write
//! to memory, ssd or disk, and should be as fast as the hardware allow for.
//! The only required in memory data structure with a write lock is the index,
//! which should be fast to update.
//!
//! [`AppendVec`]'s only store accounts for single slots.  To bootstrap the
//! index from a persistent store of [`AppendVec`]'s, the entries include
//! a "write_version".  A single global atomic `AccountsDb::write_version`
//! tracks the number of commits to the entire data store. So the latest
//! commit for each slot entry would be indexed.

mod geyser_plugin_utils;
mod scan_account_storage;
pub mod stats;
pub mod tests;

#[cfg(test)]
use crate::append_vec::StoredAccountMeta;
#[cfg(feature = "dev-context-only-utils")]
use qualifier_attr::qualifiers;
use {
    crate::{
        account_info::{AccountInfo, Offset, StorageLocation},
        account_storage::{
            stored_account_info::{StoredAccountInfo, StoredAccountInfoWithoutData},
            AccountStorage, AccountStorageStatus, ShrinkInProgress,
        },
        accounts_cache::{AccountsCache, CachedAccount, SlotCache},
        accounts_db::stats::{
            AccountsStats, CleanAccountsStats, FlushStats, PurgeStats, ShrinkAncientStats,
            ShrinkStats, ShrinkStatsSub, StoreAccountsTiming,
        },
        accounts_file::{
            AccountsFile, AccountsFileError, AccountsFileProvider, MatchAccountOwnerError,
            StorageAccess,
        },
        accounts_hash::{
            AccountHash, AccountLtHash, AccountsDeltaHash, AccountsHash, AccountsHashKind,
            AccountsHasher, AccountsLtHash, CalcAccountsHashConfig, CalculateHashIntermediate,
            HashStats, IncrementalAccountsHash, SerdeAccountsDeltaHash, SerdeAccountsHash,
            SerdeIncrementalAccountsHash, ZeroLamportAccounts, ZERO_LAMPORT_ACCOUNT_HASH,
            ZERO_LAMPORT_ACCOUNT_LT_HASH,
        },
        accounts_index::{
            in_mem_accounts_index::StartupStats, AccountSecondaryIndexes, AccountsIndex,
            AccountsIndexConfig, AccountsIndexRootsStats, AccountsIndexScanResult, DiskIndexValue,
            IndexKey, IndexValue, IsCached, RefCount, ScanConfig, ScanFilter, ScanResult, SlotList,
            UpsertReclaim, ACCOUNTS_INDEX_CONFIG_FOR_BENCHMARKS, ACCOUNTS_INDEX_CONFIG_FOR_TESTING,
        },
        accounts_index_storage::Startup,
        accounts_update_notifier_interface::AccountsUpdateNotifier,
        active_stats::{ActiveStatItem, ActiveStats},
        ancestors::Ancestors,
        ancient_append_vecs::get_ancient_append_vec_capacity,
        append_vec::{aligned_stored_size, IndexInfo, IndexInfoInner, STORE_META_OVERHEAD},
        cache_hash_data::{CacheHashData, DeletionPolicy as CacheHashDeletionPolicy},
        contains::Contains,
        is_zero_lamport::IsZeroLamport,
        partitioned_rewards::{
            PartitionedEpochRewardsConfig, DEFAULT_PARTITIONED_EPOCH_REWARDS_CONFIG,
        },
        read_only_accounts_cache::ReadOnlyAccountsCache,
        sorted_storages::SortedStorages,
        storable_accounts::{StorableAccounts, StorableAccountsBySlot},
        u64_align, utils,
        verify_accounts_hash_in_background::VerifyAccountsHashInBackground,
    },
    crossbeam_channel::{unbounded, Receiver, Sender, TryRecvError},
    dashmap::{DashMap, DashSet},
    log::*,
    rand::{thread_rng, Rng},
    rayon::{prelude::*, ThreadPool},
    seqlock::SeqLock,
    smallvec::SmallVec,
    solana_account::{Account, AccountSharedData, ReadableAccount},
    solana_clock::{BankId, Epoch, Slot},
    solana_epoch_schedule::EpochSchedule,
    solana_hash::Hash,
    solana_lattice_hash::lt_hash::LtHash,
    solana_measure::{meas_dur, measure::Measure, measure_us},
    solana_nohash_hasher::{BuildNoHashHasher, IntMap, IntSet},
    solana_pubkey::Pubkey,
    solana_rayon_threadlimit::get_thread_count,
    solana_transaction::sanitized::SanitizedTransaction,
    std::{
        borrow::Cow,
        boxed::Box,
        collections::{BTreeSet, HashMap, HashSet, VecDeque},
        fs,
        hash::{Hash as StdHash, Hasher as StdHasher},
        io, iter, mem,
        num::{NonZeroUsize, Saturating},
        ops::{Range, RangeBounds},
        path::{Path, PathBuf},
        sync::{
            atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering},
            Arc, Condvar, Mutex, RwLock,
        },
        thread::{sleep, Builder},
        time::{Duration, Instant},
    },
    tempfile::TempDir,
};

// when the accounts write cache exceeds this many bytes, we will flush it
// this can be specified on the command line, too (--accounts-db-cache-limit-mb)
const WRITE_CACHE_LIMIT_BYTES_DEFAULT: u64 = 15_000_000_000;
const SCAN_SLOT_PAR_ITER_THRESHOLD: usize = 4000;

const UNREF_ACCOUNTS_BATCH_SIZE: usize = 10_000;

const DEFAULT_FILE_SIZE: u64 = 4 * 1024 * 1024;
const DEFAULT_NUM_DIRS: u32 = 4;

// When calculating hashes, it is helpful to break the pubkeys found into bins based on the pubkey value.
// More bins means smaller vectors to sort, copy, etc.
pub const DEFAULT_HASH_CALCULATION_PUBKEY_BINS: usize = 65536;

// Without chunks, we end up with 1 output vec for each outer snapshot storage.
// This results in too many vectors to be efficient.
// Chunks when scanning storages to calculate hashes.
// If this is too big, we don't get enough parallelism of scanning storages.
// If this is too small, then we produce too many output vectors to iterate.
// Metrics indicate a sweet spot in the 2.5k-5k range for mnb.
const MAX_ITEMS_PER_CHUNK: Slot = 2_500;

// When getting accounts for shrinking from the index, this is the # of accounts to lookup per thread.
// This allows us to split up accounts index accesses across multiple threads.
const SHRINK_COLLECT_CHUNK_SIZE: usize = 50;

/// The number of shrink candidate slots that is small enough so that
/// additional storages from ancient slots can be added to the
/// candidates for shrinking.
const SHRINK_INSERT_ANCIENT_THRESHOLD: usize = 10;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ScanAccountStorageData {
    /// callback for accounts in storage will not include `data`
    // Note, currently only used in tests, but do not remove.
    #[cfg_attr(not(test), allow(dead_code))]
    NoData,
    /// return data (&[u8]) for each account.
    /// This can be expensive to get and is not necessary for many scan operations.
    DataRefForStorage,
}

#[derive(Default, Debug)]
/// hold alive accounts
/// alive means in the accounts index
pub(crate) struct AliveAccounts<'a> {
    /// slot the accounts are currently stored in
    pub(crate) slot: Slot,
    pub(crate) accounts: Vec<&'a AccountFromStorage>,
    pub(crate) bytes: usize,
}

/// separate pubkeys into those with a single refcount and those with > 1 refcount
#[derive(Debug)]
pub(crate) struct ShrinkCollectAliveSeparatedByRefs<'a> {
    /// accounts where ref_count = 1
    pub(crate) one_ref: AliveAccounts<'a>,
    /// account where ref_count > 1, but this slot contains the alive entry with the highest slot
    pub(crate) many_refs_this_is_newest_alive: AliveAccounts<'a>,
    /// account where ref_count > 1, and this slot is NOT the highest alive entry in the index for the pubkey
    pub(crate) many_refs_old_alive: AliveAccounts<'a>,
}

/// Configuration Parameters for running accounts hash and total lamports verification
#[derive(Debug, Clone)]
pub struct VerifyAccountsHashAndLamportsConfig<'a> {
    /// bank ancestors
    pub ancestors: &'a Ancestors,
    /// epoch_schedule
    pub epoch_schedule: &'a EpochSchedule,
    /// epoch
    pub epoch: Epoch,
    /// true to ignore mismatches
    pub ignore_mismatch: bool,
    /// true to dump debug log if mismatch happens
    pub store_detailed_debug_info: bool,
    /// true to use dedicated background thread pool for verification
    pub use_bg_thread_pool: bool,
}

pub(crate) trait ShrinkCollectRefs<'a>: Sync + Send {
    fn with_capacity(capacity: usize, slot: Slot) -> Self;
    fn collect(&mut self, other: Self);
    fn add(
        &mut self,
        ref_count: u64,
        account: &'a AccountFromStorage,
        slot_list: &[(Slot, AccountInfo)],
    );
    fn len(&self) -> usize;
    fn alive_bytes(&self) -> usize;
    fn alive_accounts(&self) -> &Vec<&'a AccountFromStorage>;
}

impl<'a> ShrinkCollectRefs<'a> for AliveAccounts<'a> {
    fn collect(&mut self, mut other: Self) {
        self.bytes = self.bytes.saturating_add(other.bytes);
        self.accounts.append(&mut other.accounts);
    }
    fn with_capacity(capacity: usize, slot: Slot) -> Self {
        Self {
            accounts: Vec::with_capacity(capacity),
            bytes: 0,
            slot,
        }
    }
    fn add(
        &mut self,
        _ref_count: u64,
        account: &'a AccountFromStorage,
        _slot_list: &[(Slot, AccountInfo)],
    ) {
        self.accounts.push(account);
        self.bytes = self.bytes.saturating_add(account.stored_size());
    }
    fn len(&self) -> usize {
        self.accounts.len()
    }
    fn alive_bytes(&self) -> usize {
        self.bytes
    }
    fn alive_accounts(&self) -> &Vec<&'a AccountFromStorage> {
        &self.accounts
    }
}

impl<'a> ShrinkCollectRefs<'a> for ShrinkCollectAliveSeparatedByRefs<'a> {
    fn collect(&mut self, other: Self) {
        self.one_ref.collect(other.one_ref);
        self.many_refs_this_is_newest_alive
            .collect(other.many_refs_this_is_newest_alive);
        self.many_refs_old_alive.collect(other.many_refs_old_alive);
    }
    fn with_capacity(capacity: usize, slot: Slot) -> Self {
        Self {
            one_ref: AliveAccounts::with_capacity(capacity, slot),
            many_refs_this_is_newest_alive: AliveAccounts::with_capacity(0, slot),
            many_refs_old_alive: AliveAccounts::with_capacity(0, slot),
        }
    }
    fn add(
        &mut self,
        ref_count: u64,
        account: &'a AccountFromStorage,
        slot_list: &[(Slot, AccountInfo)],
    ) {
        let other = if ref_count == 1 {
            &mut self.one_ref
        } else if slot_list.len() == 1
            || !slot_list
                .iter()
                .any(|(slot_list_slot, _info)| slot_list_slot > &self.many_refs_old_alive.slot)
        {
            // this entry is alive but is newer than any other slot in the index
            &mut self.many_refs_this_is_newest_alive
        } else {
            // This entry is alive but is older than at least one other slot in the index.
            // We would expect clean to get rid of the entry for THIS slot at some point, but clean hasn't done that yet.
            &mut self.many_refs_old_alive
        };
        other.add(ref_count, account, slot_list);
    }
    fn len(&self) -> usize {
        self.one_ref
            .len()
            .saturating_add(self.many_refs_old_alive.len())
            .saturating_add(self.many_refs_this_is_newest_alive.len())
    }
    fn alive_bytes(&self) -> usize {
        self.one_ref
            .alive_bytes()
            .saturating_add(self.many_refs_old_alive.alive_bytes())
            .saturating_add(self.many_refs_this_is_newest_alive.alive_bytes())
    }
    fn alive_accounts(&self) -> &Vec<&'a AccountFromStorage> {
        unimplemented!("illegal use");
    }
}

pub enum StoreReclaims {
    /// normal reclaim mode
    Default,
    /// do not return reclaims from accounts index upsert
    Ignore,
}

/// specifies how to return zero lamport accounts from a load
#[derive(Clone, Copy)]
enum LoadZeroLamports {
    /// return None if loaded account has zero lamports
    None,
    /// return Some(account with zero lamports) if loaded account has zero lamports
    /// This used to be the only behavior.
    /// Note that this is non-deterministic if clean is running asynchronously.
    /// If a zero lamport account exists in the index, then Some is returned.
    /// Once it is cleaned from the index, None is returned.
    #[cfg(feature = "dev-context-only-utils")]
    SomeWithZeroLamportAccountForTests,
}

#[derive(Debug)]
pub(crate) struct ShrinkCollect<'a, T: ShrinkCollectRefs<'a>> {
    pub(crate) slot: Slot,
    pub(crate) capacity: u64,
    pub(crate) pubkeys_to_unref: Vec<&'a Pubkey>,
    pub(crate) zero_lamport_single_ref_pubkeys: Vec<&'a Pubkey>,
    pub(crate) alive_accounts: T,
    /// total size in storage of all alive accounts
    pub(crate) alive_total_bytes: usize,
    pub(crate) total_starting_accounts: usize,
    /// true if all alive accounts are zero lamports
    pub(crate) all_are_zero_lamports: bool,
}

pub const ACCOUNTS_DB_CONFIG_FOR_TESTING: AccountsDbConfig = AccountsDbConfig {
    index: Some(ACCOUNTS_INDEX_CONFIG_FOR_TESTING),
    account_indexes: None,
    base_working_path: None,
    accounts_hash_cache_path: None,
    shrink_paths: None,
    shrink_ratio: DEFAULT_ACCOUNTS_SHRINK_THRESHOLD_OPTION,
    read_cache_limit_bytes: None,
    read_cache_evict_sample_size: None,
    write_cache_limit_bytes: None,
    ancient_append_vec_offset: None,
    ancient_storage_ideal_size: None,
    max_ancient_storages: None,
    skip_initial_hash_calc: false,
    exhaustively_verify_refcounts: false,
    partitioned_epoch_rewards_config: DEFAULT_PARTITIONED_EPOCH_REWARDS_CONFIG,
    storage_access: StorageAccess::File,
    scan_filter_for_shrinking: ScanFilter::OnlyAbnormalTest,
    snapshots_use_experimental_accumulator_hash: false,
    num_clean_threads: None,
    num_foreground_threads: None,
    num_hash_threads: None,
    hash_calculation_pubkey_bins: Some(4),
};
pub const ACCOUNTS_DB_CONFIG_FOR_BENCHMARKS: AccountsDbConfig = AccountsDbConfig {
    index: Some(ACCOUNTS_INDEX_CONFIG_FOR_BENCHMARKS),
    account_indexes: None,
    base_working_path: None,
    accounts_hash_cache_path: None,
    shrink_paths: None,
    shrink_ratio: DEFAULT_ACCOUNTS_SHRINK_THRESHOLD_OPTION,
    read_cache_limit_bytes: None,
    read_cache_evict_sample_size: None,
    write_cache_limit_bytes: None,
    ancient_append_vec_offset: None,
    ancient_storage_ideal_size: None,
    max_ancient_storages: None,
    skip_initial_hash_calc: false,
    exhaustively_verify_refcounts: false,
    partitioned_epoch_rewards_config: DEFAULT_PARTITIONED_EPOCH_REWARDS_CONFIG,
    storage_access: StorageAccess::File,
    scan_filter_for_shrinking: ScanFilter::OnlyAbnormal,
    snapshots_use_experimental_accumulator_hash: false,
    num_clean_threads: None,
    num_foreground_threads: None,
    num_hash_threads: None,
    hash_calculation_pubkey_bins: None,
};

pub type BinnedHashData = Vec<Vec<CalculateHashIntermediate>>;

struct LoadAccountsIndexForShrink<'a, T: ShrinkCollectRefs<'a>> {
    /// all alive accounts
    alive_accounts: T,
    /// pubkeys that are going to be unref'd in the accounts index after we are
    /// done with shrinking, because they are dead
    pubkeys_to_unref: Vec<&'a Pubkey>,
    /// pubkeys that are the last remaining zero lamport instance of an account
    zero_lamport_single_ref_pubkeys: Vec<&'a Pubkey>,
    /// true if all alive accounts are zero lamport accounts
    all_are_zero_lamports: bool,
}

/// reference an account found during scanning a storage. This is a byval struct to replace
/// `StoredAccountMeta`
#[derive(Debug, PartialEq, Copy, Clone)]
pub struct AccountFromStorage {
    pub index_info: AccountInfo,
    pub data_len: u64,
    pub pubkey: Pubkey,
}

impl IsZeroLamport for AccountFromStorage {
    fn is_zero_lamport(&self) -> bool {
        self.index_info.is_zero_lamport()
    }
}

impl AccountFromStorage {
    pub fn pubkey(&self) -> &Pubkey {
        &self.pubkey
    }
    pub fn stored_size(&self) -> usize {
        aligned_stored_size(self.data_len as usize)
    }
    pub fn data_len(&self) -> usize {
        self.data_len as usize
    }
    #[cfg(test)]
    pub fn new(account: &StoredAccountMeta) -> Self {
        // the id is irrelevant in this account info. This structure is only used DURING shrink operations.
        // In those cases, there is only 1 append vec id per slot when we read the accounts.
        // Any value of storage id in account info works fine when we want the 'normal' storage.
        let storage_id = 0;
        AccountFromStorage {
            index_info: AccountInfo::new(
                StorageLocation::AppendVec(storage_id, account.offset()),
                account.is_zero_lamport(),
            ),
            pubkey: *account.pubkey(),
            data_len: account.data_len() as u64,
        }
    }
}

pub struct GetUniqueAccountsResult {
    pub stored_accounts: Vec<AccountFromStorage>,
    pub capacity: u64,
    pub num_duplicated_accounts: usize,
}

pub struct AccountsAddRootTiming {
    pub index_us: u64,
    pub cache_us: u64,
    pub store_us: u64,
}

/// Slots older the "number of slots in an epoch minus this number"
/// than max root are treated as ancient and subject to packing.
/// |  older  |<-          slots in an epoch          ->| max root
/// |  older  |<-    offset   ->|                       |
/// |          ancient          |        modern         |
///
/// If this is negative, this many slots older than the number of
/// slots in epoch are still treated as modern (ie. non-ancient).
/// |  older  |<- abs(offset) ->|<- slots in an epoch ->| max root
/// | ancient |                 modern                  |
///
/// Note that another constant DEFAULT_MAX_ANCIENT_STORAGES sets a
/// threshold for combining ancient storages so that their overall
/// number is under a certain limit, whereas this constant establishes
/// the distance from the max root slot beyond which storages holding
/// the account data for the slots are considered ancient by the
/// shrinking algorithm.
const ANCIENT_APPEND_VEC_DEFAULT_OFFSET: Option<i64> = Some(100_000);
/// The smallest size of ideal ancient storage.
/// The setting can be overridden on the command line
/// with --accounts-db-ancient-ideal-storage-size option.
const DEFAULT_ANCIENT_STORAGE_IDEAL_SIZE: u64 = 100_000;
/// Default value for the number of ancient storages the ancient slot
/// combining should converge to.
pub const DEFAULT_MAX_ANCIENT_STORAGES: usize = 100_000;

#[derive(Debug, Default, Clone)]
pub struct AccountsDbConfig {
    pub index: Option<AccountsIndexConfig>,
    pub account_indexes: Option<AccountSecondaryIndexes>,
    /// Base directory for various necessary files
    pub base_working_path: Option<PathBuf>,
    pub accounts_hash_cache_path: Option<PathBuf>,
    pub shrink_paths: Option<Vec<PathBuf>>,
    pub shrink_ratio: AccountShrinkThreshold,
    /// The low and high watermark sizes for the read cache, in bytes.
    /// If None, defaults will be used.
    pub read_cache_limit_bytes: Option<(usize, usize)>,
    /// The number of elements that will be randomly sampled at eviction time,
    /// the oldest of which will get evicted.
    pub read_cache_evict_sample_size: Option<usize>,
    pub write_cache_limit_bytes: Option<u64>,
    /// if None, ancient append vecs are set to ANCIENT_APPEND_VEC_DEFAULT_OFFSET
    /// Some(offset) means include slots up to (max_slot - (slots_per_epoch - 'offset'))
    pub ancient_append_vec_offset: Option<i64>,
    pub ancient_storage_ideal_size: Option<u64>,
    pub max_ancient_storages: Option<usize>,
    pub hash_calculation_pubkey_bins: Option<usize>,
    pub skip_initial_hash_calc: bool,
    pub exhaustively_verify_refcounts: bool,
    pub partitioned_epoch_rewards_config: PartitionedEpochRewardsConfig,
    pub storage_access: StorageAccess,
    pub scan_filter_for_shrinking: ScanFilter,
    pub snapshots_use_experimental_accumulator_hash: bool,
    /// Number of threads for background cleaning operations (`thread_pool_clean')
    pub num_clean_threads: Option<NonZeroUsize>,
    /// Number of threads for foreground operations (`thread_pool`)
    pub num_foreground_threads: Option<NonZeroUsize>,
    /// Number of threads for background accounts hashing (`thread_pool_hash`)
    pub num_hash_threads: Option<NonZeroUsize>,
}

#[cfg(not(test))]
const ABSURD_CONSECUTIVE_FAILED_ITERATIONS: usize = 100;

#[derive(Debug, Clone, Copy)]
pub enum AccountShrinkThreshold {
    /// Measure the total space sparseness across all candidates
    /// And select the candidates by using the top sparse account storage entries to shrink.
    /// The value is the overall shrink threshold measured as ratio of the total live bytes
    /// over the total bytes.
    TotalSpace { shrink_ratio: f64 },
    /// Use the following option to shrink all stores whose alive ratio is below
    /// the specified threshold.
    IndividualStore { shrink_ratio: f64 },
}
pub const DEFAULT_ACCOUNTS_SHRINK_OPTIMIZE_TOTAL_SPACE: bool = true;
pub const DEFAULT_ACCOUNTS_SHRINK_RATIO: f64 = 0.80;
// The default extra account space in percentage from the ideal target
const DEFAULT_ACCOUNTS_SHRINK_THRESHOLD_OPTION: AccountShrinkThreshold =
    AccountShrinkThreshold::TotalSpace {
        shrink_ratio: DEFAULT_ACCOUNTS_SHRINK_RATIO,
    };

impl Default for AccountShrinkThreshold {
    fn default() -> AccountShrinkThreshold {
        DEFAULT_ACCOUNTS_SHRINK_THRESHOLD_OPTION
    }
}

pub enum ScanStorageResult<R, B> {
    Cached(Vec<R>),
    Stored(B),
}

#[derive(Debug, Default)]
pub struct IndexGenerationInfo {
    pub accounts_data_len: u64,
    /// The lt hash of the old/duplicate accounts identified during index generation.
    /// Will be used when verifying the accounts lt hash, after rebuilding a Bank.
    pub duplicates_lt_hash: Option<Box<DuplicatesLtHash>>,
}

#[derive(Debug, Default)]
struct SlotIndexGenerationInfo {
    insert_time_us: u64,
    num_accounts: u64,
    accounts_data_len: u64,
    zero_lamport_pubkeys: Vec<Pubkey>,
    all_accounts_are_zero_lamports: bool,
    /// Number of accounts in this slot that didn't already exist in the index
    num_did_not_exist: u64,
    /// Number of accounts in this slot that already existed, and were in-mem
    num_existed_in_mem: u64,
    /// Number of accounts in this slot that already existed, and were on-disk
    num_existed_on_disk: u64,
}

/// The lt hash of old/duplicate accounts
///
/// Accumulation of all the duplicate accounts found during index generation.
/// These accounts need to have their lt hashes mixed *out*.
/// This is the final value, that when applied to all the storages at startup,
/// will produce the correct accounts lt hash.
#[derive(Debug, Clone)]
pub struct DuplicatesLtHash(pub LtHash);

impl Default for DuplicatesLtHash {
    fn default() -> Self {
        Self(LtHash::identity())
    }
}

#[derive(Default, Debug)]
struct GenerateIndexTimings {
    pub total_time_us: u64,
    pub index_time: u64,
    pub scan_time: u64,
    pub insertion_time_us: u64,
    pub storage_size_storages_us: u64,
    pub index_flush_us: u64,
    pub total_including_duplicates: u64,
    pub accounts_data_len_dedup_time_us: u64,
    pub total_duplicate_slot_keys: u64,
    pub total_num_unique_duplicate_keys: u64,
    pub num_duplicate_accounts: u64,
    pub populate_duplicate_keys_us: u64,
    pub total_slots: u64,
    pub par_duplicates_lt_hash_us: AtomicU64,
    pub visit_zero_lamports_us: u64,
    pub num_zero_lamport_single_refs: u64,
    pub all_accounts_are_zero_lamports_slots: u64,
}

#[derive(Default, Debug, PartialEq, Eq)]
struct StorageSizeAndCount {
    /// total size stored, including both alive and dead bytes
    pub stored_size: usize,
    /// number of accounts in the storage including both alive and dead accounts
    pub count: usize,
}
type StorageSizeAndCountMap =
    DashMap<AccountsFileId, StorageSizeAndCount, BuildNoHashHasher<AccountsFileId>>;

impl GenerateIndexTimings {
    pub fn report(&self, startup_stats: &StartupStats) {
        datapoint_info!(
            "generate_index",
            ("overall_us", self.total_time_us, i64),
            // we cannot accurately measure index insertion time because of many threads and lock contention
            ("total_us", self.index_time, i64),
            ("scan_stores_us", self.scan_time, i64),
            ("insertion_time_us", self.insertion_time_us, i64),
            (
                "storage_size_storages_us",
                self.storage_size_storages_us,
                i64
            ),
            ("index_flush_us", self.index_flush_us, i64),
            (
                "total_items_including_duplicates",
                self.total_including_duplicates,
                i64
            ),
            (
                "accounts_data_len_dedup_time_us",
                self.accounts_data_len_dedup_time_us,
                i64
            ),
            (
                "total_duplicate_slot_keys",
                self.total_duplicate_slot_keys,
                i64
            ),
            (
                "total_num_unique_duplicate_keys",
                self.total_num_unique_duplicate_keys,
                i64
            ),
            ("num_duplicate_accounts", self.num_duplicate_accounts, i64),
            (
                "populate_duplicate_keys_us",
                self.populate_duplicate_keys_us,
                i64
            ),
            ("total_slots", self.total_slots, i64),
            (
                "copy_data_us",
                startup_stats.copy_data_us.swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "par_duplicates_lt_hash_us",
                self.par_duplicates_lt_hash_us.load(Ordering::Relaxed),
                i64
            ),
            (
                "num_zero_lamport_single_refs",
                self.num_zero_lamport_single_refs,
                i64
            ),
            ("visit_zero_lamports_us", self.visit_zero_lamports_us, i64),
            (
                "all_accounts_are_zero_lamports_slots",
                self.all_accounts_are_zero_lamports_slots,
                i64
            ),
        );
    }
}

impl IndexValue for AccountInfo {}
impl DiskIndexValue for AccountInfo {}

impl IsZeroLamport for AccountSharedData {
    fn is_zero_lamport(&self) -> bool {
        self.lamports() == 0
    }
}

impl IsZeroLamport for Account {
    fn is_zero_lamport(&self) -> bool {
        self.lamports() == 0
    }
}

struct MultiThreadProgress<'a> {
    last_update: Instant,
    my_last_report_count: u64,
    total_count: &'a AtomicU64,
    report_delay_secs: u64,
    first_caller: bool,
    ultimate_count: u64,
    start_time: Instant,
}

impl<'a> MultiThreadProgress<'a> {
    fn new(total_count: &'a AtomicU64, report_delay_secs: u64, ultimate_count: u64) -> Self {
        Self {
            last_update: Instant::now(),
            my_last_report_count: 0,
            total_count,
            report_delay_secs,
            first_caller: false,
            ultimate_count,
            start_time: Instant::now(),
        }
    }
    fn report(&mut self, my_current_count: u64) {
        let now = Instant::now();
        if now.duration_since(self.last_update).as_secs() >= self.report_delay_secs {
            let my_total_newly_processed_slots_since_last_report =
                my_current_count - self.my_last_report_count;

            self.my_last_report_count = my_current_count;
            let previous_total_processed_slots_across_all_threads = self.total_count.fetch_add(
                my_total_newly_processed_slots_since_last_report,
                Ordering::Relaxed,
            );
            self.first_caller =
                self.first_caller || 0 == previous_total_processed_slots_across_all_threads;
            if self.first_caller {
                let total = previous_total_processed_slots_across_all_threads
                    + my_total_newly_processed_slots_since_last_report;
                info!(
                    "generating index: {}/{} slots... ({}/s)",
                    total,
                    self.ultimate_count,
                    total / self.start_time.elapsed().as_secs().max(1),
                );
            }
            self.last_update = now;
        }
    }
}

/// An offset into the AccountsDb::storage vector
pub type AtomicAccountsFileId = AtomicU32;
pub type AccountsFileId = u32;

type AccountSlots = HashMap<Pubkey, IntSet<Slot>>;
type SlotOffsets = IntMap<Slot, IntSet<Offset>>;
type ReclaimResult = (AccountSlots, SlotOffsets);
type PubkeysRemovedFromAccountsIndex = HashSet<Pubkey>;
type ShrinkCandidates = IntSet<Slot>;

// Some hints for applicability of additional sanity checks for the do_load fast-path;
// Slower fallback code path will be taken if the fast path has failed over the retry
// threshold, regardless of these hints. Also, load cannot fail not-deterministically
// even under very rare circumstances, unlike previously did allow.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoadHint {
    // Caller hints that it's loading transactions for a block which is
    // descended from the current root, and at the tip of its fork.
    // Thereby, further this assumes AccountIndex::max_root should not increase
    // during this load, meaning there should be no squash.
    // Overall, this enables us to assert!() strictly while running the fast-path for
    // account loading, while maintaining the determinism of account loading and resultant
    // transaction execution thereof.
    FixedMaxRoot,
    /// same as `FixedMaxRoot`, except do not populate the read cache on load
    FixedMaxRootDoNotPopulateReadCache,
    // Caller can't hint the above safety assumption. Generally RPC and miscellaneous
    // other call-site falls into this category. The likelihood of slower path is slightly
    // increased as well.
    Unspecified,
}

#[derive(Debug)]
pub enum LoadedAccountAccessor<'a> {
    // StoredAccountMeta can't be held directly here due to its lifetime dependency to
    // AccountStorageEntry
    Stored(Option<(Arc<AccountStorageEntry>, usize)>),
    // None value in Cached variant means the cache was flushed
    Cached(Option<Cow<'a, Arc<CachedAccount>>>),
}

impl LoadedAccountAccessor<'_> {
    fn check_and_get_loaded_account_shared_data(&mut self) -> AccountSharedData {
        // all of these following .expect() and .unwrap() are like serious logic errors,
        // ideal for representing this as rust type system....

        match self {
            LoadedAccountAccessor::Stored(Some((maybe_storage_entry, offset))) => {
                // If we do find the storage entry, we can guarantee that the storage entry is
                // safe to read from because we grabbed a reference to the storage entry while it
                // was still in the storage map. This means even if the storage entry is removed
                // from the storage map after we grabbed the storage entry, the recycler should not
                // reset the storage entry until we drop the reference to the storage entry.
                maybe_storage_entry
                    .accounts
                    .get_account_shared_data(*offset)
                    .expect(
                        "If a storage entry was found in the storage map, it must not have been \
                         reset yet",
                    )
            }
            _ => self.check_and_get_loaded_account(|loaded_account| loaded_account.take_account()),
        }
    }

    fn check_and_get_loaded_account<T>(
        &mut self,
        callback: impl for<'local> FnMut(LoadedAccount<'local>) -> T,
    ) -> T {
        // all of these following .expect() and .unwrap() are like serious logic errors,
        // ideal for representing this as rust type system....

        match self {
            LoadedAccountAccessor::Cached(None) | LoadedAccountAccessor::Stored(None) => {
                panic!(
                    "Should have already been taken care of when creating this \
                     LoadedAccountAccessor"
                );
            }
            LoadedAccountAccessor::Cached(Some(_cached_account)) => {
                // Cached(Some(x)) variant always produces `Some` for get_loaded_account() since
                // it just returns the inner `x` without additional fetches
                self.get_loaded_account(callback).unwrap()
            }
            LoadedAccountAccessor::Stored(Some(_maybe_storage_entry)) => {
                // If we do find the storage entry, we can guarantee that the storage entry is
                // safe to read from because we grabbed a reference to the storage entry while it
                // was still in the storage map. This means even if the storage entry is removed
                // from the storage map after we grabbed the storage entry, the recycler should not
                // reset the storage entry until we drop the reference to the storage entry.
                self.get_loaded_account(callback).expect(
                    "If a storage entry was found in the storage map, it must not have been reset \
                     yet",
                )
            }
        }
    }

    fn get_loaded_account<T>(
        &mut self,
        mut callback: impl for<'local> FnMut(LoadedAccount<'local>) -> T,
    ) -> Option<T> {
        match self {
            LoadedAccountAccessor::Cached(cached_account) => {
                let cached_account = cached_account.take().expect(
                    "Cache flushed/purged should be handled before trying to fetch account",
                );
                Some(callback(LoadedAccount::Cached(cached_account)))
            }
            LoadedAccountAccessor::Stored(maybe_storage_entry) => {
                // storage entry may not be present if slot was cleaned up in
                // between reading the accounts index and calling this function to
                // get account meta from the storage entry here
                maybe_storage_entry
                    .as_ref()
                    .and_then(|(storage_entry, offset)| {
                        storage_entry
                            .accounts
                            .get_stored_account_callback(*offset, |account| {
                                callback(LoadedAccount::Stored(account))
                            })
                    })
            }
        }
    }

    fn account_matches_owners(&self, owners: &[Pubkey]) -> Result<usize, MatchAccountOwnerError> {
        match self {
            LoadedAccountAccessor::Cached(cached_account) => cached_account
                .as_ref()
                .and_then(|cached_account| {
                    if cached_account.account.is_zero_lamport() {
                        None
                    } else {
                        owners
                            .iter()
                            .position(|entry| cached_account.account.owner() == entry)
                    }
                })
                .ok_or(MatchAccountOwnerError::NoMatch),
            LoadedAccountAccessor::Stored(maybe_storage_entry) => {
                // storage entry may not be present if slot was cleaned up in
                // between reading the accounts index and calling this function to
                // get account meta from the storage entry here
                maybe_storage_entry
                    .as_ref()
                    .map(|(storage_entry, offset)| {
                        storage_entry
                            .accounts
                            .account_matches_owners(*offset, owners)
                    })
                    .unwrap_or(Err(MatchAccountOwnerError::UnableToLoad))
            }
        }
    }
}

pub enum LoadedAccount<'a> {
    Stored(StoredAccountInfo<'a>),
    Cached(Cow<'a, Arc<CachedAccount>>),
}

impl LoadedAccount<'_> {
    pub fn loaded_hash(&self) -> AccountHash {
        match self {
            LoadedAccount::Stored(_stored_account) => {
                // The account hash is no longer stored, so it is always the default value.
                // Callers that want the account hash must (and do) check if the value is
                // "missing", i.e. the default value, and then call hash_account() themselves.
                AccountHash(Hash::default())
            }
            LoadedAccount::Cached(cached_account) => cached_account.hash(),
        }
    }

    pub fn pubkey(&self) -> &Pubkey {
        match self {
            LoadedAccount::Stored(stored_account) => stored_account.pubkey(),
            LoadedAccount::Cached(cached_account) => cached_account.pubkey(),
        }
    }

    pub fn take_account(&self) -> AccountSharedData {
        match self {
            LoadedAccount::Stored(stored_account) => stored_account.to_account_shared_data(),
            LoadedAccount::Cached(cached_account) => match cached_account {
                Cow::Owned(cached_account) => cached_account.account.clone(),
                Cow::Borrowed(cached_account) => cached_account.account.clone(),
            },
        }
    }

    pub fn is_cached(&self) -> bool {
        match self {
            LoadedAccount::Stored(_) => false,
            LoadedAccount::Cached(_) => true,
        }
    }

    /// data_len can be calculated without having access to `&data` in future implementations
    pub fn data_len(&self) -> usize {
        self.data().len()
    }
}

impl ReadableAccount for LoadedAccount<'_> {
    fn lamports(&self) -> u64 {
        match self {
            LoadedAccount::Stored(stored_account) => stored_account.lamports(),
            LoadedAccount::Cached(cached_account) => cached_account.account.lamports(),
        }
    }
    fn data(&self) -> &[u8] {
        match self {
            LoadedAccount::Stored(stored_account) => stored_account.data(),
            LoadedAccount::Cached(cached_account) => cached_account.account.data(),
        }
    }
    fn owner(&self) -> &Pubkey {
        match self {
            LoadedAccount::Stored(stored_account) => stored_account.owner(),
            LoadedAccount::Cached(cached_account) => cached_account.account.owner(),
        }
    }
    fn executable(&self) -> bool {
        match self {
            LoadedAccount::Stored(stored_account) => stored_account.executable(),
            LoadedAccount::Cached(cached_account) => cached_account.account.executable(),
        }
    }
    fn rent_epoch(&self) -> Epoch {
        match self {
            LoadedAccount::Stored(stored_account) => stored_account.rent_epoch(),
            LoadedAccount::Cached(cached_account) => cached_account.account.rent_epoch(),
        }
    }
    fn to_account_shared_data(&self) -> AccountSharedData {
        self.take_account()
    }
}

#[derive(Debug)]
pub enum AccountsHashVerificationError {
    MissingAccountsHash,
    MismatchedAccountsHash,
    MismatchedTotalLamports(u64, u64),
}

#[derive(Default)]
struct CleanKeyTimings {
    collect_delta_keys_us: u64,
    delta_insert_us: u64,
    dirty_store_processing_us: u64,
    delta_key_count: u64,
    dirty_pubkeys_count: u64,
    oldest_dirty_slot: Slot,
    /// number of ancient append vecs that were scanned because they were dirty when clean started
    dirty_ancient_stores: usize,
}

/// Persistent storage structure holding the accounts
#[derive(Debug)]
pub struct AccountStorageEntry {
    pub(crate) id: AccountsFileId,

    pub(crate) slot: Slot,

    /// storage holding the accounts
    pub accounts: AccountsFile,

    /// Keeps track of the number of accounts stored in a specific AppendVec.
    ///  This is periodically checked to reuse the stores that do not have
    ///  any accounts in it
    /// status corresponding to the storage, lets us know that
    ///  the append_vec, once maxed out, then emptied, can be reclaimed
    count_and_status: SeqLock<(usize, AccountStorageStatus)>,

    alive_bytes: AtomicUsize,

    /// offsets to accounts that are zero lamport single ref stored in this
    /// storage. These are still alive. But, shrink will be able to remove them.
    ///
    /// NOTE: It's possible that one of these zero lamport single ref accounts
    /// could be written in a new transaction (and later rooted & flushed) and a
    /// later clean runs and marks this account dead before this storage gets a
    /// chance to be shrunk, thus making the account dead in both "alive_bytes"
    /// and as a zero lamport single ref. If this happens, we will count this
    /// account as "dead" twice. However, this should be fine. It just makes
    /// shrink more likely to visit this storage.
    zero_lamport_single_ref_offsets: RwLock<IntSet<Offset>>,

    /// Obsolete Accounts. These are accounts that are still present in the storage
    /// but should be ignored during rebuild. They have been removed
    /// from the accounts index, so they will not be picked up by scan.
    /// Slot is the slot at which the account is no longer needed.
    /// Two scenarios cause an account entry to be marked obsolete
    /// 1. The account was rewritten to a newer slot
    /// 2. The account was set to zero lamports and is older than the last
    ///    full snapshot. In this case, slot is set to the snapshot slot
    obsolete_accounts: RwLock<Vec<(Offset, usize, Slot)>>,
}

impl AccountStorageEntry {
    pub fn new(
        path: &Path,
        slot: Slot,
        id: AccountsFileId,
        file_size: u64,
        provider: AccountsFileProvider,
    ) -> Self {
        let tail = AccountsFile::file_name(slot, id);
        let path = Path::new(path).join(tail);
        let accounts = provider.new_writable(path, file_size);

        Self {
            id,
            slot,
            accounts,
            count_and_status: SeqLock::new((0, AccountStorageStatus::Available)),
            alive_bytes: AtomicUsize::new(0),
            zero_lamport_single_ref_offsets: RwLock::default(),
            obsolete_accounts: RwLock::default(),
        }
    }

    /// open a new instance of the storage that is readonly
    #[cfg_attr(feature = "dev-context-only-utils", qualifiers(pub))]
    fn reopen_as_readonly(&self, storage_access: StorageAccess) -> Option<Self> {
        if storage_access != StorageAccess::File {
            // if we are only using mmap, then no reason to re-open
            return None;
        }

        let count_and_status = self.count_and_status.lock_write();
        self.accounts.reopen_as_readonly().map(|accounts| Self {
            id: self.id,
            slot: self.slot,
            count_and_status: SeqLock::new(*count_and_status),
            alive_bytes: AtomicUsize::new(self.alive_bytes()),
            accounts,
            zero_lamport_single_ref_offsets: RwLock::default(),
            obsolete_accounts: RwLock::new(self.obsolete_accounts.read().unwrap().clone()),
        })
    }

    pub fn new_existing(slot: Slot, id: AccountsFileId, accounts: AccountsFile) -> Self {
        Self {
            id,
            slot,
            accounts,
            count_and_status: SeqLock::new((0, AccountStorageStatus::Available)),
            alive_bytes: AtomicUsize::new(0),
            zero_lamport_single_ref_offsets: RwLock::default(),
            obsolete_accounts: RwLock::default(),
        }
    }

    pub fn set_status(&self, mut status: AccountStorageStatus) {
        let mut count_and_status = self.count_and_status.lock_write();

        let count = count_and_status.0;

        if status == AccountStorageStatus::Full && count == 0 {
            // this case arises when the append_vec is full (store_ptrs fails),
            //  but all accounts have already been removed from the storage
            //
            // the only time it's safe to call reset() on an append_vec is when
            //  every account has been removed
            //          **and**
            //  the append_vec has previously been completely full
            //
            self.accounts.reset();
            status = AccountStorageStatus::Available;
        }

        *count_and_status = (count, status);
    }

    pub fn status(&self) -> AccountStorageStatus {
        self.count_and_status.read().1
    }

    pub fn count(&self) -> usize {
        self.count_and_status.read().0
    }

    pub fn alive_bytes(&self) -> usize {
        self.alive_bytes.load(Ordering::Acquire)
    }

    /// Marks the accounts at the given offsets as obsolete
    pub fn mark_accounts_obsolete(
        &self,
        newly_obsolete_accounts: impl ExactSizeIterator<Item = (Offset, usize)>,
        slot: Slot,
    ) {
        let mut obsolete_accounts_list = self.obsolete_accounts.write().unwrap();
        obsolete_accounts_list.reserve(newly_obsolete_accounts.len());

        for (offset, data_len) in newly_obsolete_accounts {
            obsolete_accounts_list.push((offset, data_len, slot));
        }
    }

    /// Returns the accounts that were marked obsolete as of the passed in slot
    /// or earlier. If slot is None, then slot will be assumed to be the max root
    /// and all obsolete accounts will be returned.
    pub fn get_obsolete_accounts(&self, slot: Option<Slot>) -> Vec<(Offset, usize)> {
        self.obsolete_accounts
            .read()
            .unwrap()
            .iter()
            .filter(|(_, _, obsolete_slot)| slot.is_none_or(|s| *obsolete_slot <= s))
            .map(|(offset, data_len, _)| (*offset, *data_len))
            .collect()
    }

    /// Returns the number of bytes that were marked obsolete as of the passed
    /// in slot or earlier. If slot is None, then slot will be assumed to be the
    /// max root, and all obsolete bytes will be returned.
    pub fn get_obsolete_bytes(&self, slot: Option<Slot>) -> usize {
        let obsolete_accounts = self.obsolete_accounts.read().unwrap();
        let obsolete_bytes = obsolete_accounts
            .iter()
            .filter(|(_, _, obsolete_slot)| slot.is_none_or(|s| *obsolete_slot <= s))
            .map(|(offset, data_len, _)| {
                self.accounts
                    .calculate_stored_size(*data_len)
                    .min(self.accounts.len() - offset)
            })
            .sum();
        obsolete_bytes
    }

    /// Return true if offset is "new" and inserted successfully. Otherwise,
    /// return false if the offset exists already.
    fn insert_zero_lamport_single_ref_account_offset(&self, offset: usize) -> bool {
        let mut zero_lamport_single_ref_offsets =
            self.zero_lamport_single_ref_offsets.write().unwrap();
        zero_lamport_single_ref_offsets.insert(offset)
    }

    /// Return the number of zero_lamport_single_ref accounts in the storage.
    fn num_zero_lamport_single_ref_accounts(&self) -> usize {
        self.zero_lamport_single_ref_offsets.read().unwrap().len()
    }

    /// Return the "alive_bytes" minus "zero_lamport_single_ref_accounts bytes".
    fn alive_bytes_exclude_zero_lamport_single_ref_accounts(&self) -> usize {
        let zero_lamport_dead_bytes = self
            .accounts
            .dead_bytes_due_to_zero_lamport_single_ref(self.num_zero_lamport_single_ref_accounts());
        self.alive_bytes().saturating_sub(zero_lamport_dead_bytes)
    }

    pub fn written_bytes(&self) -> u64 {
        self.accounts.len() as u64
    }

    pub fn capacity(&self) -> u64 {
        self.accounts.capacity()
    }

    pub fn has_accounts(&self) -> bool {
        self.count() > 0
    }

    pub fn slot(&self) -> Slot {
        self.slot
    }

    pub fn id(&self) -> AccountsFileId {
        self.id
    }

    pub fn flush(&self) -> Result<(), AccountsFileError> {
        self.accounts.flush()
    }

    fn add_accounts(&self, num_accounts: usize, num_bytes: usize) {
        let mut count_and_status = self.count_and_status.lock_write();
        *count_and_status = (count_and_status.0 + num_accounts, count_and_status.1);
        self.alive_bytes.fetch_add(num_bytes, Ordering::Release);
    }

    /// returns # of accounts remaining in the storage
    fn remove_accounts(&self, num_bytes: usize, num_accounts: usize) -> usize {
        let mut count_and_status = self.count_and_status.lock_write();
        let (mut count, mut status) = *count_and_status;

        if count == num_accounts && status == AccountStorageStatus::Full {
            // this case arises when we remove the last account from the
            //  storage, but we've learned from previous write attempts that
            //  the storage is full
            //
            // the only time it's safe to call reset() on an append_vec is when
            //  every account has been removed
            //          **and**
            //  the append_vec has previously been completely full
            //
            // otherwise, the storage may be in flight with a store()
            //   call
            self.accounts.reset();
            status = AccountStorageStatus::Available;
        }

        // Some code path is removing accounts too many; this may result in an
        // unintended reveal of old state for unrelated accounts.
        assert!(
            count >= num_accounts,
            "double remove of account in slot: {}/store: {}!!",
            self.slot(),
            self.id(),
        );

        self.alive_bytes.fetch_sub(num_bytes, Ordering::Release);
        count = count.saturating_sub(num_accounts);
        *count_and_status = (count, status);
        count
    }

    /// Returns the path to the underlying accounts storage file
    pub fn path(&self) -> &Path {
        self.accounts.path()
    }
}

pub fn get_temp_accounts_paths(count: u32) -> io::Result<(Vec<TempDir>, Vec<PathBuf>)> {
    let temp_dirs: io::Result<Vec<TempDir>> = (0..count).map(|_| TempDir::new()).collect();
    let temp_dirs = temp_dirs?;

    let paths: io::Result<Vec<_>> = temp_dirs
        .iter()
        .map(|temp_dir| {
            utils::create_accounts_run_and_snapshot_dirs(temp_dir)
                .map(|(run_dir, _snapshot_dir)| run_dir)
        })
        .collect();
    let paths = paths?;
    Ok((temp_dirs, paths))
}

#[derive(Default, Debug)]
struct CleaningInfo {
    slot_list: SlotList<AccountInfo>,
    ref_count: u64,
    /// Indicates if this account might have a zero lamport index entry.
    /// If false, the account *shall* not have zero lamport index entries.
    /// If true, the account *might* have zero lamport index entries.
    might_contain_zero_lamport_entry: bool,
}

/// This is the return type of AccountsDb::construct_candidate_clean_keys.
/// It's a collection of pubkeys with associated information to
/// facilitate the decision making about which accounts can be removed
/// from the accounts index. In addition, the minimal dirty slot is
/// included in the returned value.
type CleaningCandidates = (Box<[RwLock<HashMap<Pubkey, CleaningInfo>>]>, Option<Slot>);

/// Removing unrooted slots in Accounts Background Service needs to be synchronized with flushing
/// slots from the Accounts Cache.  This keeps track of those slots and the Mutex + Condvar for
/// synchronization.
#[derive(Debug, Default)]
struct RemoveUnrootedSlotsSynchronization {
    // slots being flushed from the cache or being purged
    slots_under_contention: Mutex<IntSet<Slot>>,
    signal: Condvar,
}

type AccountInfoAccountsIndex = AccountsIndex<AccountInfo, AccountInfo>;

// This structure handles the load/store of the accounts
#[derive(Debug)]
pub struct AccountsDb {
    /// Keeps tracks of index into AppendVec on a per slot basis
    pub accounts_index: AccountInfoAccountsIndex,

    /// Some(offset) iff we want to squash old append vecs together into 'ancient append vecs'
    /// Some(offset) means for slots up to (max_slot - (slots_per_epoch - 'offset')), put them in ancient append vecs
    pub ancient_append_vec_offset: Option<i64>,
    pub ancient_storage_ideal_size: u64,
    pub max_ancient_storages: usize,
    /// true iff we want to skip the initial hash calculation on startup
    pub skip_initial_hash_calc: bool,

    /// The number of pubkey bins used for accounts hash calculation
    pub hash_calculation_pubkey_bins: usize,

    pub storage: AccountStorage,

    pub accounts_cache: AccountsCache,

    write_cache_limit_bytes: Option<u64>,

    sender_bg_hasher: RwLock<Option<Sender<Vec<Arc<CachedAccount>>>>>,
    read_only_accounts_cache: ReadOnlyAccountsCache,

    /// distribute the accounts across storage lists
    pub next_id: AtomicAccountsFileId,

    /// Set of shrinkable stores organized by map of slot to storage id
    pub shrink_candidate_slots: Mutex<ShrinkCandidates>,

    pub write_version: AtomicU64,

    /// Set of storage paths to pick from
    pub paths: Vec<PathBuf>,

    /// Base directory for various necessary files
    base_working_path: PathBuf,
    // used by tests - held until we are dropped
    #[allow(dead_code)]
    base_working_temp_dir: Option<TempDir>,

    accounts_hash_cache_path: PathBuf,

    shrink_paths: Vec<PathBuf>,

    /// Directory of paths this accounts_db needs to hold/remove
    #[allow(dead_code)]
    pub temp_paths: Option<Vec<TempDir>>,

    /// Starting file size of appendvecs
    file_size: u64,

    /// Foreground thread pool used for par_iter
    pub thread_pool: ThreadPool,
    /// Thread pool for AccountsBackgroundServices
    pub thread_pool_clean: ThreadPool,
    /// Thread pool for AccountsHashVerifier
    pub thread_pool_hash: ThreadPool,

    accounts_delta_hashes: Mutex<HashMap<Slot, AccountsDeltaHash>>,
    accounts_hashes: Mutex<HashMap<Slot, (AccountsHash, /*capitalization*/ u64)>>,
    incremental_accounts_hashes:
        Mutex<HashMap<Slot, (IncrementalAccountsHash, /*capitalization*/ u64)>>,

    pub stats: AccountsStats,

    clean_accounts_stats: CleanAccountsStats,

    // Stats for purges called outside of clean_accounts()
    external_purge_slots_stats: PurgeStats,

    pub shrink_stats: ShrinkStats,

    pub(crate) shrink_ancient_stats: ShrinkAncientStats,

    pub account_indexes: AccountSecondaryIndexes,

    /// Set of unique keys per slot which is used
    /// to drive clean_accounts
    /// Populated when flushing the accounts write cache
    uncleaned_pubkeys: DashMap<Slot, Vec<Pubkey>, BuildNoHashHasher<Slot>>,

    #[cfg(test)]
    load_delay: u64,

    #[cfg(test)]
    load_limit: AtomicU64,

    /// true if drop_callback is attached to the bank.
    is_bank_drop_callback_enabled: AtomicBool,

    /// Set of slots currently being flushed by `flush_slot_cache()` or removed
    /// by `remove_unrooted_slot()`. Used to ensure `remove_unrooted_slots(slots)`
    /// can safely clear the set of unrooted slots `slots`.
    remove_unrooted_slots_synchronization: RemoveUnrootedSlotsSynchronization,

    shrink_ratio: AccountShrinkThreshold,

    /// Set of stores which are recently rooted or had accounts removed
    /// such that potentially a 0-lamport account update could be present which
    /// means we can remove the account from the index entirely.
    dirty_stores: DashMap<Slot, Arc<AccountStorageEntry>, BuildNoHashHasher<Slot>>,

    /// Zero-lamport accounts that are *not* purged during clean because they need to stay alive
    /// for incremental snapshot support.
    zero_lamport_accounts_to_purge_after_full_snapshot: DashSet<(Slot, Pubkey)>,

    /// GeyserPlugin accounts update notifier
    accounts_update_notifier: Option<AccountsUpdateNotifier>,

    pub(crate) active_stats: ActiveStats,

    pub verify_accounts_hash_in_bg: VerifyAccountsHashInBackground,

    /// Used to disable logging dead slots during removal.
    /// allow disabling noisy log
    pub log_dead_slots: AtomicBool,

    /// debug feature to scan every append vec and verify refcounts are equal
    exhaustively_verify_refcounts: bool,

    /// storage format to use for new storages
    accounts_file_provider: AccountsFileProvider,

    /// method to use for accessing storages
    storage_access: StorageAccess,

    /// index scan filtering for shrinking
    scan_filter_for_shrinking: ScanFilter,

    /// this will live here until the feature for partitioned epoch rewards is activated.
    /// At that point, this and other code can be deleted.
    pub partitioned_epoch_rewards_config: PartitionedEpochRewardsConfig,

    /// The latest full snapshot slot dictates how to handle zero lamport accounts
    /// Note, this is None if we're told to *not* take snapshots
    latest_full_snapshot_slot: SeqLock<Option<Slot>>,

    /// Flag to indicate if the experimental accounts lattice hash is used for snapshots.
    /// (For R&D only; a feature-gate also exists to turn this on.)
    pub snapshots_use_experimental_accumulator_hash: AtomicBool,

    /// These are the ancient storages that could be valuable to
    /// shrink, sorted by amount of dead bytes.  The elements
    /// are sorted from the largest dead bytes to the smallest.
    /// Members are Slot and capacity. If capacity is smaller, then
    /// that means the storage was already shrunk.
    pub(crate) best_ancient_slots_to_shrink: RwLock<VecDeque<(Slot, u64)>>,
}

/// results from 'split_storages_ancient'
#[derive(Debug, Default, PartialEq)]
struct SplitAncientStorages {
    /// # ancient slots
    ancient_slot_count: usize,
    /// the specific ancient slots
    ancient_slots: Vec<Slot>,
    /// lowest slot that is not an ancient append vec
    first_non_ancient_slot: Slot,
    /// slot # of beginning of first aligned chunk starting from the first non ancient slot
    first_chunk_start: Slot,
    /// # non-ancient slots to scan
    non_ancient_slot_count: usize,
    /// # chunks to use to iterate the storages
    /// all ancient chunks, the special 0 and last chunks for non-full chunks, and all the 'full' chunks of normal slots
    chunk_count: usize,
    /// start and end(exclusive) of normal (non-ancient) slots to be scanned
    normal_slot_range: Range<Slot>,
}

impl SplitAncientStorages {
    /// When calculating accounts hash, we break the slots/storages into chunks that remain the same during an entire epoch.
    /// a slot is in this chunk of slots:
    /// start:         (slot / MAX_ITEMS_PER_CHUNK) * MAX_ITEMS_PER_CHUNK
    /// end_exclusive: start + MAX_ITEMS_PER_CHUNK
    /// So a slot remains in the same chunk whenever it is included in the accounts hash.
    /// When the slot gets deleted or gets consumed in an ancient append vec, it will no longer be in its chunk.
    /// The results of scanning a chunk of appendvecs can be cached to avoid scanning large amounts of data over and over.
    fn new(oldest_non_ancient_slot: Option<Slot>, snapshot_storages: &SortedStorages) -> Self {
        let range = snapshot_storages.range();

        let (ancient_slots, first_non_ancient_slot) = if let Some(oldest_non_ancient_slot) =
            oldest_non_ancient_slot
        {
            // any ancient append vecs should definitely be cached
            // We need to break the ranges into:
            // 1. individual ancient append vecs (may be empty)
            // 2. first unevenly divided chunk starting at 1 epoch old slot (may be empty)
            // 3. evenly divided full chunks in the middle
            // 4. unevenly divided chunk of most recent slots (may be empty)
            let ancient_slots =
                Self::get_ancient_slots(oldest_non_ancient_slot, snapshot_storages, |storage| {
                    storage.capacity() > get_ancient_append_vec_capacity() * 50 / 100
                });

            let first_non_ancient_slot = ancient_slots
                .last()
                .map(|last_ancient_slot| last_ancient_slot.saturating_add(1))
                .unwrap_or(range.start);

            (ancient_slots, first_non_ancient_slot)
        } else {
            (vec![], range.start)
        };

        Self::new_with_ancient_info(range, ancient_slots, first_non_ancient_slot)
    }

    /// return all ancient append vec slots from the early slots referenced by 'snapshot_storages'
    /// `treat_as_ancient` returns true if the storage at this slot is large and should be treated individually by accounts hash calculation.
    /// `treat_as_ancient` is a fn so that we can test this well. Otherwise, we have to generate large append vecs to pass the intended checks.
    fn get_ancient_slots(
        oldest_non_ancient_slot: Slot,
        snapshot_storages: &SortedStorages,
        treat_as_ancient: impl Fn(&AccountStorageEntry) -> bool,
    ) -> Vec<Slot> {
        let range = snapshot_storages.range();
        let mut i = 0;
        let mut len_truncate = 0;
        let mut possible_ancient_slots = snapshot_storages
            .iter_range(&(range.start..oldest_non_ancient_slot))
            .filter_map(|(slot, storage)| {
                storage.map(|storage| {
                    i += 1;
                    if treat_as_ancient(storage) {
                        // even though the slot is in range of being an ancient append vec, if it isn't actually a large append vec,
                        // then we are better off treating all these slots as normally cacheable to reduce work in dedup.
                        // Since this one is large, for the moment, this one becomes the highest slot where we want to individually cache files.
                        len_truncate = i;
                    }
                    slot
                })
            })
            .collect::<Vec<_>>();
        possible_ancient_slots.truncate(len_truncate);
        possible_ancient_slots
    }

    /// create once ancient slots have been identified
    /// This is easier to test, removing SortedStorages as a type to deal with here.
    fn new_with_ancient_info(
        range: &Range<Slot>,
        ancient_slots: Vec<Slot>,
        first_non_ancient_slot: Slot,
    ) -> Self {
        if range.is_empty() {
            // Corner case mainly for tests, but gives us a consistent base case. Makes more sense to return default here than anything else.
            // caller is asking to split for empty set of slots
            return SplitAncientStorages::default();
        }

        let max_slot_inclusive = range.end.saturating_sub(1);
        let ancient_slot_count = ancient_slots.len();
        let first_chunk_start = ((first_non_ancient_slot + MAX_ITEMS_PER_CHUNK)
            / MAX_ITEMS_PER_CHUNK)
            * MAX_ITEMS_PER_CHUNK;

        let non_ancient_slot_count = (max_slot_inclusive - first_non_ancient_slot + 1) as usize;

        let normal_slot_range = Range {
            start: first_non_ancient_slot,
            end: range.end,
        };

        // 2 is for 2 special chunks - unaligned slots at the beginning and end
        let chunk_count =
            ancient_slot_count + 2 + non_ancient_slot_count / (MAX_ITEMS_PER_CHUNK as usize);

        SplitAncientStorages {
            ancient_slot_count,
            ancient_slots,
            first_non_ancient_slot,
            first_chunk_start,
            non_ancient_slot_count,
            chunk_count,
            normal_slot_range,
        }
    }

    /// given 'normal_chunk', return the starting slot of that chunk in the normal/non-ancient range
    /// a normal_chunk is 0<=normal_chunk<=non_ancient_chunk_count
    /// non_ancient_chunk_count is chunk_count-ancient_slot_count
    fn get_starting_slot_from_normal_chunk(&self, normal_chunk: usize) -> Slot {
        if normal_chunk == 0 {
            self.normal_slot_range.start
        } else {
            assert!(
                normal_chunk.saturating_add(self.ancient_slot_count) < self.chunk_count,
                "out of bounds: {}, {}",
                normal_chunk,
                self.chunk_count
            );

            let normal_chunk = normal_chunk.saturating_sub(1);
            (self.first_chunk_start + MAX_ITEMS_PER_CHUNK * (normal_chunk as Slot))
                .max(self.normal_slot_range.start)
        }
    }

    /// ancient slots are the first chunks
    fn is_chunk_ancient(&self, chunk: usize) -> bool {
        chunk < self.ancient_slot_count
    }

    /// given chunk in 0<=chunk<self.chunk_count
    /// return the range of slots in that chunk
    /// None indicates the range is empty for that chunk.
    fn get_slot_range(&self, chunk: usize) -> Option<Range<Slot>> {
        let range = if self.is_chunk_ancient(chunk) {
            // ancient append vecs are handled individually
            let slot = self.ancient_slots[chunk];
            Range {
                start: slot,
                end: slot + 1,
            }
        } else {
            // normal chunks are after ancient chunks
            let normal_chunk = chunk - self.ancient_slot_count;
            if normal_chunk == 0 {
                // first slot
                Range {
                    start: self.normal_slot_range.start,
                    end: self.first_chunk_start.min(self.normal_slot_range.end),
                }
            } else {
                // normal full chunk or the last chunk
                let first_slot = self.get_starting_slot_from_normal_chunk(normal_chunk);
                Range {
                    start: first_slot,
                    end: (first_slot + MAX_ITEMS_PER_CHUNK).min(self.normal_slot_range.end),
                }
            }
        };
        // return empty range as None
        (!range.is_empty()).then_some(range)
    }
}

pub fn quarter_thread_count() -> usize {
    std::cmp::max(2, num_cpus::get() / 4)
}

pub fn make_min_priority_thread_pool() -> ThreadPool {
    // Use lower thread count to reduce priority.
    let num_threads = quarter_thread_count();
    rayon::ThreadPoolBuilder::new()
        .thread_name(|i| format!("solAccountsLo{i:02}"))
        .num_threads(num_threads)
        .build()
        .unwrap()
}

/// Returns the default number of threads to use for background accounts hashing
pub fn default_num_hash_threads() -> NonZeroUsize {
    // 1/8 of the number of cpus and up to 6 threads gives good balance for the system.
    let num_threads = (num_cpus::get() / 8).clamp(2, 6);
    NonZeroUsize::new(num_threads).unwrap()
}

pub fn make_hash_thread_pool(num_threads: Option<NonZeroUsize>) -> ThreadPool {
    let num_threads = num_threads.unwrap_or_else(default_num_hash_threads).get();
    rayon::ThreadPoolBuilder::new()
        .thread_name(|i| format!("solAcctHash{i:02}"))
        .num_threads(num_threads)
        .build()
        .unwrap()
}

pub fn default_num_foreground_threads() -> usize {
    get_thread_count()
}

#[cfg(feature = "frozen-abi")]
impl solana_frozen_abi::abi_example::AbiExample for AccountsDb {
    fn example() -> Self {
        let accounts_db = AccountsDb::new_single_for_tests();
        let key = Pubkey::default();
        let some_data_len = 5;
        let some_slot: Slot = 0;
        let account = AccountSharedData::new(1, some_data_len, &key);
        accounts_db.store_for_tests(some_slot, &[(&key, &account)]);
        accounts_db.add_root_and_flush_write_cache(0);
        accounts_db
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PubkeyHashAccount {
    pub pubkey: Pubkey,
    pub hash: AccountHash,
    pub account: AccountSharedData,
}

impl AccountsDb {
    pub const DEFAULT_ACCOUNTS_HASH_CACHE_DIR: &'static str = "accounts_hash_cache";

    // The default high and low watermark sizes for the accounts read cache.
    // If the cache size exceeds MAX_SIZE_HI, it'll evict entries until the size is <= MAX_SIZE_LO.
    #[cfg_attr(feature = "dev-context-only-utils", qualifiers(pub))]
    const DEFAULT_MAX_READ_ONLY_CACHE_DATA_SIZE_LO: usize = 400 * 1024 * 1024;
    #[cfg_attr(feature = "dev-context-only-utils", qualifiers(pub))]
    const DEFAULT_MAX_READ_ONLY_CACHE_DATA_SIZE_HI: usize = 410 * 1024 * 1024;

    // See AccountsDbConfig::read_cache_evict_sample_size.
    #[cfg_attr(feature = "dev-context-only-utils", qualifiers(pub))]
    const DEFAULT_READ_ONLY_CACHE_EVICT_SAMPLE_SIZE: usize = 8;

    pub fn default_for_tests() -> Self {
        Self::new_single_for_tests()
    }

    pub fn new_single_for_tests() -> Self {
        AccountsDb::new_for_tests(Vec::new())
    }

    pub fn new_single_for_tests_with_provider(file_provider: AccountsFileProvider) -> Self {
        AccountsDb::new_for_tests_with_provider(Vec::new(), file_provider)
    }

    pub fn new_for_tests(paths: Vec<PathBuf>) -> Self {
        Self::new_for_tests_with_provider(paths, AccountsFileProvider::default())
    }

    fn new_for_tests_with_provider(
        paths: Vec<PathBuf>,
        accounts_file_provider: AccountsFileProvider,
    ) -> Self {
        let mut db = AccountsDb::new_with_config(
            paths,
            Some(ACCOUNTS_DB_CONFIG_FOR_TESTING),
            None,
            Arc::default(),
        );
        db.accounts_file_provider = accounts_file_provider;
        db
    }

    pub fn new_with_config(
        paths: Vec<PathBuf>,
        accounts_db_config: Option<AccountsDbConfig>,
        accounts_update_notifier: Option<AccountsUpdateNotifier>,
        exit: Arc<AtomicBool>,
    ) -> Self {
        let accounts_db_config = accounts_db_config.unwrap_or_default();
        let accounts_index_config = accounts_db_config.index.unwrap_or_default();
        let accounts_index = AccountsIndex::new(&accounts_index_config, exit);

        let base_working_path = accounts_db_config.base_working_path.clone();
        let (base_working_path, base_working_temp_dir) =
            if let Some(base_working_path) = base_working_path {
                (base_working_path, None)
            } else {
                let base_working_temp_dir = TempDir::new().unwrap();
                let base_working_path = base_working_temp_dir.path().to_path_buf();
                (base_working_path, Some(base_working_temp_dir))
            };

        let (paths, temp_paths) = if paths.is_empty() {
            // Create a temporary set of accounts directories, used primarily
            // for testing
            let (temp_dirs, temp_paths) = get_temp_accounts_paths(DEFAULT_NUM_DIRS).unwrap();
            (temp_paths, Some(temp_dirs))
        } else {
            (paths, None)
        };

        let shrink_paths = accounts_db_config
            .shrink_paths
            .clone()
            .unwrap_or_else(|| paths.clone());

        let accounts_hash_cache_path = accounts_db_config.accounts_hash_cache_path.clone();
        let accounts_hash_cache_path = accounts_hash_cache_path.unwrap_or_else(|| {
            let accounts_hash_cache_path =
                base_working_path.join(Self::DEFAULT_ACCOUNTS_HASH_CACHE_DIR);
            if !accounts_hash_cache_path.exists() {
                fs::create_dir(&accounts_hash_cache_path).expect("create accounts hash cache dir");
            }
            accounts_hash_cache_path
        });

        let read_cache_size = accounts_db_config.read_cache_limit_bytes.unwrap_or((
            Self::DEFAULT_MAX_READ_ONLY_CACHE_DATA_SIZE_LO,
            Self::DEFAULT_MAX_READ_ONLY_CACHE_DATA_SIZE_HI,
        ));
        let read_cache_evict_sample_size = accounts_db_config
            .read_cache_evict_sample_size
            .unwrap_or(Self::DEFAULT_READ_ONLY_CACHE_EVICT_SAMPLE_SIZE);

        // Increase the stack for foreground threads
        // rayon needs a lot of stack
        const ACCOUNTS_STACK_SIZE: usize = 8 * 1024 * 1024;
        let num_foreground_threads = accounts_db_config
            .num_foreground_threads
            .map(Into::into)
            .unwrap_or_else(default_num_foreground_threads);
        let thread_pool = rayon::ThreadPoolBuilder::new()
            .num_threads(num_foreground_threads)
            .thread_name(|i| format!("solAccounts{i:02}"))
            .stack_size(ACCOUNTS_STACK_SIZE)
            .build()
            .expect("new rayon threadpool");

        let num_clean_threads = accounts_db_config
            .num_clean_threads
            .map(Into::into)
            .unwrap_or_else(quarter_thread_count);
        let thread_pool_clean = rayon::ThreadPoolBuilder::new()
            .thread_name(|i| format!("solAccountsLo{i:02}"))
            .num_threads(num_clean_threads)
            .build()
            .expect("new rayon threadpool");

        let thread_pool_hash = make_hash_thread_pool(accounts_db_config.num_hash_threads);

        let new = Self {
            accounts_index,
            paths,
            base_working_path,
            base_working_temp_dir,
            accounts_hash_cache_path,
            temp_paths,
            shrink_paths,
            skip_initial_hash_calc: accounts_db_config.skip_initial_hash_calc,
            ancient_append_vec_offset: accounts_db_config
                .ancient_append_vec_offset
                .or(ANCIENT_APPEND_VEC_DEFAULT_OFFSET),
            ancient_storage_ideal_size: accounts_db_config
                .ancient_storage_ideal_size
                .unwrap_or(DEFAULT_ANCIENT_STORAGE_IDEAL_SIZE),
            max_ancient_storages: accounts_db_config
                .max_ancient_storages
                .unwrap_or(DEFAULT_MAX_ANCIENT_STORAGES),
            hash_calculation_pubkey_bins: accounts_db_config
                .hash_calculation_pubkey_bins
                .unwrap_or(DEFAULT_HASH_CALCULATION_PUBKEY_BINS),
            account_indexes: accounts_db_config.account_indexes.unwrap_or_default(),
            shrink_ratio: accounts_db_config.shrink_ratio,
            accounts_update_notifier,
            read_only_accounts_cache: ReadOnlyAccountsCache::new(
                read_cache_size.0,
                read_cache_size.1,
                read_cache_evict_sample_size,
            ),
            write_cache_limit_bytes: accounts_db_config.write_cache_limit_bytes,
            partitioned_epoch_rewards_config: accounts_db_config.partitioned_epoch_rewards_config,
            exhaustively_verify_refcounts: accounts_db_config.exhaustively_verify_refcounts,
            storage_access: accounts_db_config.storage_access,
            scan_filter_for_shrinking: accounts_db_config.scan_filter_for_shrinking,
            snapshots_use_experimental_accumulator_hash: accounts_db_config
                .snapshots_use_experimental_accumulator_hash
                .into(),
            thread_pool,
            thread_pool_clean,
            thread_pool_hash,
            verify_accounts_hash_in_bg: VerifyAccountsHashInBackground::default(),
            active_stats: ActiveStats::default(),
            storage: AccountStorage::default(),
            accounts_cache: AccountsCache::default(),
            sender_bg_hasher: RwLock::new(None),
            uncleaned_pubkeys: DashMap::default(),
            next_id: AtomicAccountsFileId::new(0),
            shrink_candidate_slots: Mutex::new(ShrinkCandidates::default()),
            write_version: AtomicU64::new(0),
            file_size: DEFAULT_FILE_SIZE,
            accounts_delta_hashes: Mutex::new(HashMap::new()),
            accounts_hashes: Mutex::new(HashMap::new()),
            incremental_accounts_hashes: Mutex::new(HashMap::new()),
            external_purge_slots_stats: PurgeStats::default(),
            clean_accounts_stats: CleanAccountsStats::default(),
            shrink_stats: ShrinkStats::default(),
            shrink_ancient_stats: ShrinkAncientStats::default(),
            stats: AccountsStats::default(),
            #[cfg(test)]
            load_delay: u64::default(),
            #[cfg(test)]
            load_limit: AtomicU64::default(),
            is_bank_drop_callback_enabled: AtomicBool::default(),
            remove_unrooted_slots_synchronization: RemoveUnrootedSlotsSynchronization::default(),
            dirty_stores: DashMap::default(),
            zero_lamport_accounts_to_purge_after_full_snapshot: DashSet::default(),
            log_dead_slots: AtomicBool::new(true),
            accounts_file_provider: AccountsFileProvider::default(),
            latest_full_snapshot_slot: SeqLock::new(None),
            best_ancient_slots_to_shrink: RwLock::default(),
        };

        {
            for path in new.paths.iter() {
                std::fs::create_dir_all(path).expect("Create directory failed.");
            }
        }
        new
    }

    pub fn file_size(&self) -> u64 {
        self.file_size
    }

    /// Get the base working directory
    pub fn get_base_working_path(&self) -> PathBuf {
        self.base_working_path.clone()
    }

    /// Returns true if there is an accounts update notifier.
    pub fn has_accounts_update_notifier(&self) -> bool {
        self.accounts_update_notifier.is_some()
    }

    fn next_id(&self) -> AccountsFileId {
        let next_id = self.next_id.fetch_add(1, Ordering::AcqRel);
        assert!(
            next_id != AccountsFileId::MAX,
            "We've run out of storage ids!"
        );
        next_id
    }

    fn new_storage_entry(&self, slot: Slot, path: &Path, size: u64) -> AccountStorageEntry {
        AccountStorageEntry::new(
            path,
            slot,
            self.next_id(),
            size,
            self.accounts_file_provider,
        )
    }

    /// Returns if snapshots use the experimental accounts lattice hash
    pub fn snapshots_use_experimental_accumulator_hash(&self) -> bool {
        self.snapshots_use_experimental_accumulator_hash
            .load(Ordering::Acquire)
    }

    /// Sets if snapshots use the experimental accounts lattice hash
    pub fn set_snapshots_use_experimental_accumulator_hash(&self, is_enabled: bool) {
        self.snapshots_use_experimental_accumulator_hash
            .store(is_enabled, Ordering::Release);
    }

    /// While scanning cleaning candidates obtain slots that can be
    /// reclaimed for each pubkey. In addition, if the pubkey is
    /// removed from the index, insert in pubkeys_removed_from_accounts_index.
    fn collect_reclaims(
        &self,
        pubkey: &Pubkey,
        max_clean_root_inclusive: Option<Slot>,
        ancient_account_cleans: &AtomicU64,
        epoch_schedule: &EpochSchedule,
        pubkeys_removed_from_accounts_index: &Mutex<PubkeysRemovedFromAccountsIndex>,
    ) -> SlotList<AccountInfo> {
        let one_epoch_old = self.get_oldest_non_ancient_slot(epoch_schedule);
        let mut clean_rooted = Measure::start("clean_old_root-ms");
        let mut reclaims = Vec::new();
        let removed_from_index = self.accounts_index.clean_rooted_entries(
            pubkey,
            &mut reclaims,
            max_clean_root_inclusive,
        );
        if removed_from_index {
            pubkeys_removed_from_accounts_index
                .lock()
                .unwrap()
                .insert(*pubkey);
        }
        if !reclaims.is_empty() {
            // figure out how many ancient accounts have been reclaimed
            let old_reclaims = reclaims
                .iter()
                .filter_map(|(slot, _)| (slot < &one_epoch_old).then_some(1))
                .sum();
            ancient_account_cleans.fetch_add(old_reclaims, Ordering::Relaxed);
        }
        clean_rooted.stop();
        self.clean_accounts_stats
            .clean_old_root_us
            .fetch_add(clean_rooted.as_us(), Ordering::Relaxed);
        reclaims
    }

    /// Reclaim older states of accounts older than max_clean_root_inclusive for AccountsDb bloat mitigation.
    /// Any accounts which are removed from the accounts index are returned in PubkeysRemovedFromAccountsIndex.
    /// These should NOT be unref'd later from the accounts index.
    fn clean_accounts_older_than_root(
        &self,
        reclaims: &SlotList<AccountInfo>,
        pubkeys_removed_from_accounts_index: &HashSet<Pubkey>,
    ) -> ReclaimResult {
        let mut measure = Measure::start("clean_old_root_reclaims");

        let reclaim_result = self.handle_reclaims(
            (!reclaims.is_empty()).then(|| reclaims.iter()),
            None,
            pubkeys_removed_from_accounts_index,
            HandleReclaims::ProcessDeadSlots(&self.clean_accounts_stats.purge_stats),
            MarkAccountsObsolete::No,
        );
        measure.stop();
        debug!("{measure}");
        self.clean_accounts_stats
            .clean_old_root_reclaim_us
            .fetch_add(measure.as_us(), Ordering::Relaxed);
        reclaim_result
    }

    /// increment store_counts to non-zero for all stores that can not be deleted.
    /// a store cannot be deleted if:
    /// 1. one of the pubkeys in the store has account info to a store whose store count is not going to zero
    /// 2. a pubkey we were planning to remove is not removing all stores that contain the account
    fn calc_delete_dependencies(
        &self,
        candidates: &[HashMap<Pubkey, CleaningInfo>],
        store_counts: &mut HashMap<Slot, (usize, HashSet<Pubkey>)>,
        min_slot: Option<Slot>,
    ) {
        // Another pass to check if there are some filtered accounts which
        // do not match the criteria of deleting all appendvecs which contain them
        // then increment their storage count.
        let mut already_counted = IntSet::default();
        for (bin_index, bin) in candidates.iter().enumerate() {
            for (pubkey, cleaning_info) in bin.iter() {
                let slot_list = &cleaning_info.slot_list;
                let ref_count = &cleaning_info.ref_count;
                let mut failed_slot = None;
                let all_stores_being_deleted = slot_list.len() as RefCount == *ref_count;
                if all_stores_being_deleted {
                    let mut delete = true;
                    for (slot, _account_info) in slot_list {
                        if let Some(count) = store_counts.get(slot).map(|s| s.0) {
                            debug!("calc_delete_dependencies() slot: {slot}, count len: {count}");
                            if count == 0 {
                                // this store CAN be removed
                                continue;
                            }
                        }
                        // One of the pubkeys in the store has account info to a store whose store count is not going to zero.
                        // If the store cannot be found, that also means store isn't being deleted.
                        failed_slot = Some(*slot);
                        delete = false;
                        break;
                    }
                    if delete {
                        // this pubkey can be deleted from all stores it is in
                        continue;
                    }
                } else {
                    // a pubkey we were planning to remove is not removing all stores that contain the account
                    debug!(
                        "calc_delete_dependencies(), pubkey: {pubkey}, slot list len: {}, ref \
                         count: {ref_count}, slot list: {slot_list:?}",
                        slot_list.len(),
                    );
                }

                // increment store_counts to non-zero for all stores that can not be deleted.
                let mut pending_stores = IntSet::default();
                for (slot, _account_info) in slot_list {
                    if !already_counted.contains(slot) {
                        pending_stores.insert(*slot);
                    }
                }
                while !pending_stores.is_empty() {
                    let slot = pending_stores.iter().next().cloned().unwrap();
                    if Some(slot) == min_slot {
                        if let Some(failed_slot) = failed_slot.take() {
                            info!(
                                "calc_delete_dependencies, oldest slot is not able to be deleted \
                                 because of {pubkey} in slot {failed_slot}"
                            );
                        } else {
                            info!(
                                "calc_delete_dependencies, oldest slot is not able to be deleted \
                                 because of {pubkey}, slot list len: {}, ref count: {ref_count}",
                                slot_list.len()
                            );
                        }
                    }

                    pending_stores.remove(&slot);
                    if !already_counted.insert(slot) {
                        continue;
                    }
                    // the point of all this code: remove the store count for all stores we cannot remove
                    if let Some(store_count) = store_counts.remove(&slot) {
                        // all pubkeys in this store also cannot be removed from all stores they are in
                        let affected_pubkeys = &store_count.1;
                        for key in affected_pubkeys {
                            let candidates_bin_index =
                                self.accounts_index.bin_calculator.bin_from_pubkey(key);
                            let mut update_pending_stores =
                                |bin: &HashMap<Pubkey, CleaningInfo>| {
                                    for (slot, _account_info) in &bin.get(key).unwrap().slot_list {
                                        if !already_counted.contains(slot) {
                                            pending_stores.insert(*slot);
                                        }
                                    }
                                };
                            if candidates_bin_index == bin_index {
                                update_pending_stores(bin);
                            } else {
                                update_pending_stores(&candidates[candidates_bin_index]);
                            }
                        }
                    }
                }
            }
        }
    }

    fn background_hasher(receiver: Receiver<Vec<Arc<CachedAccount>>>) {
        info!("Background account hasher has started");
        loop {
            let result = receiver.try_recv();
            match result {
                Ok(accounts) => {
                    for account in accounts {
                        // if we hold the only ref, then this account doesn't need to be hashed, we ignore this account and it will disappear
                        if Arc::strong_count(&account) > 1 {
                            // this will cause the hash to be calculated and store inside account if it needs to be calculated
                            let _ = (*account).hash();
                        };
                    }
                }
                Err(TryRecvError::Empty) => {
                    sleep(Duration::from_millis(5));
                }
                Err(err @ TryRecvError::Disconnected) => {
                    info!("Background account hasher is stopping because: {err}");
                    break;
                }
            }
        }
        info!("Background account hasher has stopped");
    }

    pub fn start_background_hasher(&self) {
        if self.is_background_hasher_running() {
            return;
        }

        let (sender, receiver) = unbounded();
        Builder::new()
            .name("solDbStoreHashr".to_string())
            .spawn(move || {
                Self::background_hasher(receiver);
            })
            .unwrap();
        *self.sender_bg_hasher.write().unwrap() = Some(sender);
    }

    pub fn stop_background_hasher(&self) {
        drop(self.sender_bg_hasher.write().unwrap().take())
    }

    pub fn is_background_hasher_running(&self) -> bool {
        self.sender_bg_hasher.read().unwrap().is_some()
    }

    #[must_use]
    pub fn purge_keys_exact<'a, C>(
        &'a self,
        pubkey_to_slot_set: impl Iterator<Item = &'a (Pubkey, C)>,
    ) -> (Vec<(Slot, AccountInfo)>, PubkeysRemovedFromAccountsIndex)
    where
        C: Contains<'a, Slot> + 'a,
    {
        let mut reclaims = Vec::new();
        let mut dead_keys = Vec::new();

        let mut purge_exact_count = 0;
        let (_, purge_exact_us) = measure_us!(for (pubkey, slots_set) in pubkey_to_slot_set {
            purge_exact_count += 1;
            let is_empty = self
                .accounts_index
                .purge_exact(pubkey, slots_set, &mut reclaims);
            if is_empty {
                dead_keys.push(pubkey);
            }
        });

        let (pubkeys_removed_from_accounts_index, handle_dead_keys_us) = measure_us!(self
            .accounts_index
            .handle_dead_keys(&dead_keys, &self.account_indexes));

        self.stats
            .purge_exact_count
            .fetch_add(purge_exact_count, Ordering::Relaxed);
        self.stats
            .handle_dead_keys_us
            .fetch_add(handle_dead_keys_us, Ordering::Relaxed);
        self.stats
            .purge_exact_us
            .fetch_add(purge_exact_us, Ordering::Relaxed);
        (reclaims, pubkeys_removed_from_accounts_index)
    }

    fn max_clean_root(&self, proposed_clean_root: Option<Slot>) -> Option<Slot> {
        match (
            self.accounts_index.min_ongoing_scan_root(),
            proposed_clean_root,
        ) {
            (None, None) => None,
            (Some(min_scan_root), None) => Some(min_scan_root),
            (None, Some(proposed_clean_root)) => Some(proposed_clean_root),
            (Some(min_scan_root), Some(proposed_clean_root)) => {
                Some(std::cmp::min(min_scan_root, proposed_clean_root))
            }
        }
    }

    /// get the oldest slot that is within one epoch of the highest known root.
    /// The slot will have been offset by `self.ancient_append_vec_offset`
    fn get_oldest_non_ancient_slot(&self, epoch_schedule: &EpochSchedule) -> Slot {
        self.get_oldest_non_ancient_slot_from_slot(
            epoch_schedule,
            self.accounts_index.max_root_inclusive(),
        )
    }

    /// get the oldest slot that is within one epoch of `max_root_inclusive`.
    /// The slot will have been offset by `self.ancient_append_vec_offset`
    fn get_oldest_non_ancient_slot_from_slot(
        &self,
        epoch_schedule: &EpochSchedule,
        max_root_inclusive: Slot,
    ) -> Slot {
        let mut result = max_root_inclusive;
        if let Some(offset) = self.ancient_append_vec_offset {
            result = Self::apply_offset_to_slot(result, offset);
        }
        result = Self::apply_offset_to_slot(
            result,
            -((epoch_schedule.slots_per_epoch as i64).saturating_sub(1)),
        );
        result.min(max_root_inclusive)
    }

    /// Collect all the uncleaned slots, up to a max slot
    ///
    /// Search through the uncleaned Pubkeys and return all the slots, up to a maximum slot.
    fn collect_uncleaned_slots_up_to_slot(&self, max_slot_inclusive: Slot) -> Vec<Slot> {
        self.uncleaned_pubkeys
            .iter()
            .filter_map(|entry| {
                let slot = *entry.key();
                (slot <= max_slot_inclusive).then_some(slot)
            })
            .collect()
    }

    /// For each slot in the list of uncleaned slots, up to a maximum
    /// slot, remove it from the `uncleaned_pubkeys` and move all the
    /// pubkeys to `candidates` for cleaning.
    fn remove_uncleaned_slots_up_to_slot_and_move_pubkeys(
        &self,
        max_slot_inclusive: Slot,
        candidates: &[RwLock<HashMap<Pubkey, CleaningInfo>>],
    ) {
        let uncleaned_slots = self.collect_uncleaned_slots_up_to_slot(max_slot_inclusive);
        for uncleaned_slot in uncleaned_slots.into_iter() {
            if let Some((_removed_slot, mut removed_pubkeys)) =
                self.uncleaned_pubkeys.remove(&uncleaned_slot)
            {
                // Sort all keys by bin index so that we can insert
                // them in `candidates` more efficiently.
                removed_pubkeys.sort_by(|a, b| {
                    self.accounts_index
                        .bin_calculator
                        .bin_from_pubkey(a)
                        .cmp(&self.accounts_index.bin_calculator.bin_from_pubkey(b))
                });
                if let Some(first_removed_pubkey) = removed_pubkeys.first() {
                    let mut prev_bin = self
                        .accounts_index
                        .bin_calculator
                        .bin_from_pubkey(first_removed_pubkey);
                    let mut candidates_bin = candidates[prev_bin].write().unwrap();
                    for removed_pubkey in removed_pubkeys {
                        let curr_bin = self
                            .accounts_index
                            .bin_calculator
                            .bin_from_pubkey(&removed_pubkey);
                        if curr_bin != prev_bin {
                            candidates_bin = candidates[curr_bin].write().unwrap();
                            prev_bin = curr_bin;
                        }
                        // Conservatively mark the candidate might have a zero lamport entry for
                        // correctness so that scan WILL try to look in disk if it is
                        // not in-mem. These keys are from 1) recently processed
                        // slots, 2) zero lamports found in shrink. Therefore, they are very likely
                        // to be in-memory, and seldomly do we need to look them up in disk.
                        candidates_bin.insert(
                            removed_pubkey,
                            CleaningInfo {
                                might_contain_zero_lamport_entry: true,
                                ..Default::default()
                            },
                        );
                    }
                }
            }
        }
    }

    fn count_pubkeys(candidates: &[RwLock<HashMap<Pubkey, CleaningInfo>>]) -> u64 {
        candidates
            .iter()
            .map(|x| x.read().unwrap().len())
            .sum::<usize>() as u64
    }

    /// Construct a list of candidates for cleaning from:
    /// - dirty_stores      -- set of stores which had accounts removed or recently rooted
    /// - uncleaned_pubkeys -- the delta set of updated pubkeys in rooted slots from the last clean
    ///
    /// The function also returns the minimum slot we encountered.
    fn construct_candidate_clean_keys(
        &self,
        max_clean_root_inclusive: Option<Slot>,
        is_startup: bool,
        timings: &mut CleanKeyTimings,
        epoch_schedule: &EpochSchedule,
    ) -> CleaningCandidates {
        let oldest_non_ancient_slot = self.get_oldest_non_ancient_slot(epoch_schedule);
        let mut dirty_store_processing_time = Measure::start("dirty_store_processing");
        let max_root_inclusive = self.accounts_index.max_root_inclusive();
        let max_slot_inclusive = max_clean_root_inclusive.unwrap_or(max_root_inclusive);
        let mut dirty_stores = Vec::with_capacity(self.dirty_stores.len());
        // find the oldest dirty slot
        // we'll add logging if that append vec cannot be marked dead
        let mut min_dirty_slot = None::<u64>;
        self.dirty_stores.retain(|slot, store| {
            if *slot > max_slot_inclusive {
                true
            } else {
                min_dirty_slot = min_dirty_slot.map(|min| min.min(*slot)).or(Some(*slot));
                dirty_stores.push((*slot, store.clone()));
                false
            }
        });
        let dirty_stores_len = dirty_stores.len();
        let num_bins = self.accounts_index.bins();
        let candidates: Box<_> =
            std::iter::repeat_with(|| RwLock::new(HashMap::<Pubkey, CleaningInfo>::new()))
                .take(num_bins)
                .collect();

        let insert_candidate = |pubkey, is_zero_lamport| {
            let index = self.accounts_index.bin_calculator.bin_from_pubkey(&pubkey);
            let mut candidates_bin = candidates[index].write().unwrap();
            candidates_bin
                .entry(pubkey)
                .or_default()
                .might_contain_zero_lamport_entry |= is_zero_lamport;
        };

        let dirty_ancient_stores = AtomicUsize::default();
        let mut dirty_store_routine = || {
            let chunk_size = 1.max(dirty_stores_len.saturating_div(rayon::current_num_threads()));
            let oldest_dirty_slots: Vec<u64> = dirty_stores
                .par_chunks(chunk_size)
                .map(|dirty_store_chunk| {
                    let mut oldest_dirty_slot = max_slot_inclusive.saturating_add(1);
                    dirty_store_chunk.iter().for_each(|(slot, store)| {
                        if *slot < oldest_non_ancient_slot {
                            dirty_ancient_stores.fetch_add(1, Ordering::Relaxed);
                        }
                        oldest_dirty_slot = oldest_dirty_slot.min(*slot);

                        store
                            .accounts
                            .scan_accounts_without_data(|_offset, account| {
                                let pubkey = *account.pubkey();
                                let is_zero_lamport = account.is_zero_lamport();
                                insert_candidate(pubkey, is_zero_lamport);
                            })
                            .expect("must scan accounts storage");
                    });
                    oldest_dirty_slot
                })
                .collect();
            timings.oldest_dirty_slot = *oldest_dirty_slots
                .iter()
                .min()
                .unwrap_or(&max_slot_inclusive.saturating_add(1));
        };

        if is_startup {
            // Free to consume all the cores during startup
            dirty_store_routine();
        } else {
            self.thread_pool_clean.install(|| {
                dirty_store_routine();
            });
        }
        timings.dirty_pubkeys_count = Self::count_pubkeys(&candidates);
        trace!(
            "dirty_stores.len: {} pubkeys.len: {}",
            dirty_stores_len,
            timings.dirty_pubkeys_count,
        );
        dirty_store_processing_time.stop();
        timings.dirty_store_processing_us += dirty_store_processing_time.as_us();
        timings.dirty_ancient_stores = dirty_ancient_stores.load(Ordering::Relaxed);

        let mut collect_delta_keys = Measure::start("key_create");
        self.remove_uncleaned_slots_up_to_slot_and_move_pubkeys(max_slot_inclusive, &candidates);
        collect_delta_keys.stop();
        timings.collect_delta_keys_us += collect_delta_keys.as_us();

        timings.delta_key_count = Self::count_pubkeys(&candidates);

        // Check if we should purge any of the
        // zero_lamport_accounts_to_purge_later, based on the
        // latest_full_snapshot_slot.
        let latest_full_snapshot_slot = self.latest_full_snapshot_slot();
        assert!(
            latest_full_snapshot_slot.is_some()
                || self
                    .zero_lamport_accounts_to_purge_after_full_snapshot
                    .is_empty(),
            "if snapshots are disabled, then zero_lamport_accounts_to_purge_later should always \
             be empty"
        );
        if let Some(latest_full_snapshot_slot) = latest_full_snapshot_slot {
            self.zero_lamport_accounts_to_purge_after_full_snapshot
                .retain(|(slot, pubkey)| {
                    let is_candidate_for_clean =
                        max_slot_inclusive >= *slot && latest_full_snapshot_slot >= *slot;
                    if is_candidate_for_clean {
                        insert_candidate(*pubkey, true);
                    }
                    !is_candidate_for_clean
                });
        }

        (candidates, min_dirty_slot)
    }

    /// Call clean_accounts() with the common parameters that tests/benches use.
    pub fn clean_accounts_for_tests(&self) {
        self.clean_accounts(None, false, &EpochSchedule::default())
    }

    /// called with cli argument to verify refcounts are correct on all accounts
    /// this is very slow
    /// this function will call Rayon par_iter, so you will want to have thread pool installed if
    /// you want to call this without consuming all the cores on the CPU.
    fn exhaustively_verify_refcounts(&self, max_slot_inclusive: Option<Slot>) {
        let max_slot_inclusive =
            max_slot_inclusive.unwrap_or_else(|| self.accounts_index.max_root_inclusive());
        info!("exhaustively verifying refcounts as of slot: {max_slot_inclusive}");
        let pubkey_refcount = DashMap::<Pubkey, Vec<Slot>>::default();
        let slots = self.storage.all_slots();
        // populate
        slots.into_par_iter().for_each(|slot| {
            if slot > max_slot_inclusive {
                return;
            }
            if let Some(storage) = self.storage.get_slot_storage_entry(slot) {
                storage
                    .accounts
                    .scan_accounts(|_offset, account| {
                        let pk = account.pubkey();
                        match pubkey_refcount.entry(*pk) {
                            dashmap::mapref::entry::Entry::Occupied(mut occupied_entry) => {
                                if !occupied_entry.get().iter().any(|s| s == &slot) {
                                    occupied_entry.get_mut().push(slot);
                                }
                            }
                            dashmap::mapref::entry::Entry::Vacant(vacant_entry) => {
                                vacant_entry.insert(vec![slot]);
                            }
                        }
                    })
                    .expect("must scan accounts storage");
            }
        });
        let total = pubkey_refcount.len();
        let failed = AtomicBool::default();
        let threads = quarter_thread_count();
        let per_batch = total / threads;
        (0..=threads).into_par_iter().for_each(|attempt| {
            pubkey_refcount
                .iter()
                .skip(attempt * per_batch)
                .take(per_batch)
                .for_each(|entry| {
                    if failed.load(Ordering::Relaxed) {
                        return;
                    }

                    self.accounts_index
                        .get_and_then(entry.key(), |index_entry| {
                            if let Some(index_entry) = index_entry {
                                match (index_entry.ref_count() as usize).cmp(&entry.value().len()) {
                                    std::cmp::Ordering::Equal => {
                                        // ref counts match, nothing to do here
                                    }
                                    std::cmp::Ordering::Greater => {
                                        let slot_list = index_entry.slot_list.read().unwrap();
                                        let num_too_new = slot_list
                                            .iter()
                                            .filter(|(slot, _)| slot > &max_slot_inclusive)
                                            .count();

                                        if ((index_entry.ref_count() as usize) - num_too_new)
                                            > entry.value().len()
                                        {
                                            failed.store(true, Ordering::Relaxed);
                                            error!(
                                                "exhaustively_verify_refcounts: {} refcount too \
                                                 large: {}, should be: {}, {:?}, {:?}, too_new: \
                                                 {num_too_new}",
                                                entry.key(),
                                                index_entry.ref_count(),
                                                entry.value().len(),
                                                *entry.value(),
                                                slot_list
                                            );
                                        }
                                    }
                                    std::cmp::Ordering::Less => {
                                        error!(
                                            "exhaustively_verify_refcounts: {} refcount too \
                                             small: {}, should be: {}, {:?}, {:?}",
                                            entry.key(),
                                            index_entry.ref_count(),
                                            entry.value().len(),
                                            *entry.value(),
                                            index_entry.slot_list.read().unwrap()
                                        );
                                    }
                                }
                            };
                            (false, ())
                        });
                });
        });
        if failed.load(Ordering::Relaxed) {
            panic!("exhaustively_verify_refcounts failed");
        }
    }

    // Purge zero lamport accounts and older rooted account states as garbage
    // collection
    // Only remove those accounts where the entire rooted history of the account
    // can be purged because there are no live append vecs in the ancestors
    pub fn clean_accounts(
        &self,
        max_clean_root_inclusive: Option<Slot>,
        is_startup: bool,
        epoch_schedule: &EpochSchedule,
    ) {
        if self.exhaustively_verify_refcounts {
            //at startup use all cores to verify refcounts
            if is_startup {
                self.exhaustively_verify_refcounts(max_clean_root_inclusive);
            } else {
                // otherwise, use the cleaning thread pool
                self.thread_pool_clean
                    .install(|| self.exhaustively_verify_refcounts(max_clean_root_inclusive));
            }
        }

        let _guard = self.active_stats.activate(ActiveStatItem::Clean);

        let ancient_account_cleans = AtomicU64::default();
        let purges_old_accounts_count = AtomicU64::default();

        let mut measure_all = Measure::start("clean_accounts");
        let max_clean_root_inclusive = self.max_clean_root(max_clean_root_inclusive);

        self.report_store_stats();

        let active_guard = self
            .active_stats
            .activate(ActiveStatItem::CleanConstructCandidates);
        let mut measure_construct_candidates = Measure::start("construct_candidates");
        let mut key_timings = CleanKeyTimings::default();
        let (mut candidates, min_dirty_slot) = self.construct_candidate_clean_keys(
            max_clean_root_inclusive,
            is_startup,
            &mut key_timings,
            epoch_schedule,
        );
        measure_construct_candidates.stop();
        drop(active_guard);

        let num_candidates = Self::count_pubkeys(&candidates);
        let found_not_zero_accum = AtomicU64::new(0);
        let not_found_on_fork_accum = AtomicU64::new(0);
        let missing_accum = AtomicU64::new(0);
        let useful_accum = AtomicU64::new(0);
        let reclaims: SlotList<AccountInfo> = Vec::with_capacity(num_candidates as usize);
        let reclaims = Mutex::new(reclaims);
        let pubkeys_removed_from_accounts_index: PubkeysRemovedFromAccountsIndex = HashSet::new();
        let pubkeys_removed_from_accounts_index = Mutex::new(pubkeys_removed_from_accounts_index);
        // parallel scan the index.
        let do_clean_scan = || {
            candidates.par_iter().for_each(|candidates_bin| {
                let mut found_not_zero = 0;
                let mut not_found_on_fork = 0;
                let mut missing = 0;
                let mut useful = 0;
                let mut purges_old_accounts_local = 0;
                let mut candidates_bin = candidates_bin.write().unwrap();
                // Iterate over each HashMap entry to
                // avoid capturing the HashMap in the
                // closure passed to scan thus making
                // conflicting read and write borrows.
                candidates_bin.retain(|candidate_pubkey, candidate_info| {
                    let mut should_collect_reclaims = false;
                    self.accounts_index.scan(
                        iter::once(candidate_pubkey),
                        |_candidate_pubkey, slot_list_and_ref_count, _entry| {
                            let mut useless = true;
                            if let Some((slot_list, ref_count)) = slot_list_and_ref_count {
                                // find the highest rooted slot in the slot list
                                let index_in_slot_list = self.accounts_index.latest_slot(
                                    None,
                                    slot_list,
                                    max_clean_root_inclusive,
                                );

                                match index_in_slot_list {
                                    Some(index_in_slot_list) => {
                                        // found info relative to max_clean_root
                                        let (slot, account_info) = &slot_list[index_in_slot_list];
                                        if account_info.is_zero_lamport() {
                                            useless = false;
                                            // The latest one is zero lamports. We may be able to purge it.
                                            // Add all the rooted entries that contain this pubkey.
                                            // We know the highest rooted entry is zero lamports.
                                            candidate_info.slot_list =
                                                self.accounts_index.get_rooted_entries(
                                                    slot_list,
                                                    max_clean_root_inclusive,
                                                );
                                            candidate_info.ref_count = ref_count;
                                        } else {
                                            found_not_zero += 1;
                                        }

                                        // If this candidate has multiple rooted slot list entries,
                                        // we should reclaim the older ones.
                                        if slot_list.len() > 1
                                            && *slot
                                                <= max_clean_root_inclusive.unwrap_or(Slot::MAX)
                                        {
                                            should_collect_reclaims = true;
                                            purges_old_accounts_local += 1;
                                            useless = false;
                                        }
                                    }
                                    None => {
                                        // This pubkey is in the index but not in a root slot, so clean
                                        // it up by adding it to the to-be-purged list.
                                        //
                                        // Also, this pubkey must have been touched by some slot since
                                        // it was in the dirty list, so we assume that the slot it was
                                        // touched in must be unrooted.
                                        not_found_on_fork += 1;
                                        should_collect_reclaims = true;
                                        purges_old_accounts_local += 1;
                                        useless = false;
                                    }
                                }
                            } else {
                                missing += 1;
                            }
                            if !useless {
                                useful += 1;
                            }
                            AccountsIndexScanResult::OnlyKeepInMemoryIfDirty
                        },
                        None,
                        false,
                        if candidate_info.might_contain_zero_lamport_entry {
                            ScanFilter::All
                        } else {
                            self.scan_filter_for_shrinking
                        },
                    );
                    if should_collect_reclaims {
                        let reclaims_new = self.collect_reclaims(
                            candidate_pubkey,
                            max_clean_root_inclusive,
                            &ancient_account_cleans,
                            epoch_schedule,
                            &pubkeys_removed_from_accounts_index,
                        );
                        if !reclaims_new.is_empty() {
                            reclaims.lock().unwrap().extend(reclaims_new);
                        }
                    }
                    !candidate_info.slot_list.is_empty()
                });
                found_not_zero_accum.fetch_add(found_not_zero, Ordering::Relaxed);
                not_found_on_fork_accum.fetch_add(not_found_on_fork, Ordering::Relaxed);
                missing_accum.fetch_add(missing, Ordering::Relaxed);
                useful_accum.fetch_add(useful, Ordering::Relaxed);
                purges_old_accounts_count.fetch_add(purges_old_accounts_local, Ordering::Relaxed);
            });
        };
        let active_guard = self
            .active_stats
            .activate(ActiveStatItem::CleanScanCandidates);
        let mut accounts_scan = Measure::start("accounts_scan");
        if is_startup {
            do_clean_scan();
        } else {
            self.thread_pool_clean.install(do_clean_scan);
        }
        accounts_scan.stop();
        drop(active_guard);

        // strip the RwLock from the candidate bins now that we no longer need it
        let mut candidates: Box<_> = candidates
            .iter_mut()
            .map(|candidates_bin| mem::take(candidates_bin.get_mut().unwrap()))
            .collect();

        let retained_keys_count: usize = candidates.iter().map(HashMap::len).sum();
        let reclaims = reclaims.into_inner().unwrap();
        let mut pubkeys_removed_from_accounts_index =
            pubkeys_removed_from_accounts_index.into_inner().unwrap();

        let active_guard = self.active_stats.activate(ActiveStatItem::CleanOldAccounts);
        let mut clean_old_rooted = Measure::start("clean_old_roots");
        let (purged_account_slots, removed_accounts) =
            self.clean_accounts_older_than_root(&reclaims, &pubkeys_removed_from_accounts_index);
        clean_old_rooted.stop();
        drop(active_guard);

        // Calculate store counts as if everything was purged
        // Then purge if we can
        let active_guard = self
            .active_stats
            .activate(ActiveStatItem::CleanCollectStoreCounts);
        let mut store_counts_time = Measure::start("store_counts");
        let mut store_counts: HashMap<Slot, (usize, HashSet<Pubkey>)> = HashMap::new();
        for candidates_bin in candidates.iter_mut() {
            for (pubkey, cleaning_info) in candidates_bin.iter_mut() {
                let slot_list = &mut cleaning_info.slot_list;
                let ref_count = &mut cleaning_info.ref_count;
                debug_assert!(!slot_list.is_empty(), "candidate slot_list can't be empty");
                if purged_account_slots.contains_key(pubkey) {
                    *ref_count = self.accounts_index.ref_count_from_storage(pubkey);
                }
                slot_list.retain(|(slot, account_info)| {
                    let was_slot_purged = purged_account_slots
                        .get(pubkey)
                        .map(|slots_removed| slots_removed.contains(slot))
                        .unwrap_or(false);
                    if was_slot_purged {
                        // No need to look up the slot storage below if the entire
                        // slot was purged
                        return false;
                    }
                    // Check if this update in `slot` to the account with `key` was reclaimed earlier by
                    // `clean_accounts_older_than_root()`
                    let was_reclaimed = removed_accounts
                        .get(slot)
                        .map(|store_removed| store_removed.contains(&account_info.offset()))
                        .unwrap_or(false);
                    if was_reclaimed {
                        return false;
                    }
                    if let Some(store_count) = store_counts.get_mut(slot) {
                        store_count.0 -= 1;
                        store_count.1.insert(*pubkey);
                    } else {
                        let mut key_set = HashSet::new();
                        key_set.insert(*pubkey);
                        assert!(
                            !account_info.is_cached(),
                            "The Accounts Cache must be flushed first for this account info. \
                             pubkey: {}, slot: {}",
                            *pubkey,
                            *slot
                        );
                        let count = self
                            .storage
                            .get_account_storage_entry(*slot, account_info.store_id())
                            .map(|store| store.count())
                            .unwrap()
                            - 1;
                        debug!(
                            "store_counts, inserting slot: {}, store id: {}, count: {}",
                            slot,
                            account_info.store_id(),
                            count
                        );
                        store_counts.insert(*slot, (count, key_set));
                    }
                    true
                });
            }
        }
        store_counts_time.stop();
        drop(active_guard);

        let active_guard = self
            .active_stats
            .activate(ActiveStatItem::CleanCalcDeleteDeps);
        let mut calc_deps_time = Measure::start("calc_deps");
        self.calc_delete_dependencies(&candidates, &mut store_counts, min_dirty_slot);
        calc_deps_time.stop();
        drop(active_guard);

        let active_guard = self
            .active_stats
            .activate(ActiveStatItem::CleanFilterZeroLamport);
        let mut purge_filter = Measure::start("purge_filter");
        self.filter_zero_lamport_clean_for_incremental_snapshots(
            max_clean_root_inclusive,
            &store_counts,
            &mut candidates,
        );
        purge_filter.stop();
        drop(active_guard);

        let active_guard = self.active_stats.activate(ActiveStatItem::CleanReclaims);
        let mut reclaims_time = Measure::start("reclaims");
        // Recalculate reclaims with new purge set
        let mut pubkey_to_slot_set = Vec::new();
        for candidates_bin in candidates.iter() {
            let mut bin_set = candidates_bin
                .iter()
                .filter_map(|(pubkey, cleaning_info)| {
                    let slot_list = &cleaning_info.slot_list;
                    (!slot_list.is_empty()).then_some((
                        *pubkey,
                        slot_list
                            .iter()
                            .map(|(slot, _)| *slot)
                            .collect::<HashSet<Slot>>(),
                    ))
                })
                .collect::<Vec<_>>();
            pubkey_to_slot_set.append(&mut bin_set);
        }

        let (reclaims, pubkeys_removed_from_accounts_index2) =
            self.purge_keys_exact(pubkey_to_slot_set.iter());
        pubkeys_removed_from_accounts_index.extend(pubkeys_removed_from_accounts_index2);

        self.handle_reclaims(
            (!reclaims.is_empty()).then(|| reclaims.iter()),
            None,
            &pubkeys_removed_from_accounts_index,
            HandleReclaims::ProcessDeadSlots(&self.clean_accounts_stats.purge_stats),
            MarkAccountsObsolete::No,
        );

        reclaims_time.stop();
        drop(active_guard);

        measure_all.stop();

        self.clean_accounts_stats.report();
        datapoint_info!(
            "clean_accounts",
            ("max_clean_root", max_clean_root_inclusive, Option<i64>),
            ("total_us", measure_all.as_us(), i64),
            (
                "collect_delta_keys_us",
                key_timings.collect_delta_keys_us,
                i64
            ),
            ("oldest_dirty_slot", key_timings.oldest_dirty_slot, i64),
            (
                "pubkeys_removed_from_accounts_index",
                pubkeys_removed_from_accounts_index.len(),
                i64
            ),
            (
                "dirty_ancient_stores",
                key_timings.dirty_ancient_stores,
                i64
            ),
            (
                "dirty_store_processing_us",
                key_timings.dirty_store_processing_us,
                i64
            ),
            ("construct_candidates_us", measure_construct_candidates.as_us(), i64),
            ("accounts_scan", accounts_scan.as_us(), i64),
            ("clean_old_rooted", clean_old_rooted.as_us(), i64),
            ("store_counts", store_counts_time.as_us(), i64),
            ("purge_filter", purge_filter.as_us(), i64),
            ("calc_deps", calc_deps_time.as_us(), i64),
            ("reclaims", reclaims_time.as_us(), i64),
            ("delta_insert_us", key_timings.delta_insert_us, i64),
            ("delta_key_count", key_timings.delta_key_count, i64),
            ("dirty_pubkeys_count", key_timings.dirty_pubkeys_count, i64),
            ("useful_keys", useful_accum.load(Ordering::Relaxed), i64),
            ("total_keys_count", num_candidates, i64),
            ("retained_keys_count", retained_keys_count, i64),
            (
                "scan_found_not_zero",
                found_not_zero_accum.load(Ordering::Relaxed),
                i64
            ),
            (
                "scan_not_found_on_fork",
                not_found_on_fork_accum.load(Ordering::Relaxed),
                i64
            ),
            ("scan_missing", missing_accum.load(Ordering::Relaxed), i64),
            (
                "get_account_sizes_us",
                self.clean_accounts_stats
                    .get_account_sizes_us
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "slots_cleaned",
                self.clean_accounts_stats
                    .slots_cleaned
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "clean_old_root_us",
                self.clean_accounts_stats
                    .clean_old_root_us
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "clean_old_root_reclaim_us",
                self.clean_accounts_stats
                    .clean_old_root_reclaim_us
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "remove_dead_accounts_remove_us",
                self.clean_accounts_stats
                    .remove_dead_accounts_remove_us
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "remove_dead_accounts_shrink_us",
                self.clean_accounts_stats
                    .remove_dead_accounts_shrink_us
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "clean_stored_dead_slots_us",
                self.clean_accounts_stats
                    .clean_stored_dead_slots_us
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "roots_added",
                self.accounts_index.roots_added.swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "purge_older_root_entries_one_slot_list",
                self.accounts_index
                    .purge_older_root_entries_one_slot_list
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "roots_removed",
                self.accounts_index.roots_removed.swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "active_scans",
                self.accounts_index.active_scans.load(Ordering::Relaxed),
                i64
            ),
            (
                "max_distance_to_min_scan_slot",
                self.accounts_index
                    .max_distance_to_min_scan_slot
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "ancient_account_cleans",
                ancient_account_cleans.load(Ordering::Relaxed),
                i64
            ),
            (
                "purges_old_accounts_count",
                purges_old_accounts_count.load(Ordering::Relaxed),
                i64
            ),
            ("next_store_id", self.next_id.load(Ordering::Relaxed), i64),
        );
    }

    /// Removes the accounts in the input `reclaims` from the tracked "count" of
    /// their corresponding  storage entries. Note this does not actually free
    /// the memory from the storage entries until all the storage entries for
    /// a given slot `S` are empty, at which point `process_dead_slots` will
    /// remove all the storage entries for `S`.
    ///
    /// # Arguments
    /// * `reclaims` - The accounts to remove from storage entries' "count". Note here
    ///   that we should not remove cache entries, only entries for accounts actually
    ///   stored in a storage entry.
    /// * `expected_single_dead_slot` - A correctness assertion. If this is equal to `Some(S)`,
    ///   then the function will check that the only slot being cleaned up in `reclaims`
    ///   is the slot == `S`. This is true for instance when `handle_reclaims` is called
    ///   from store or slot shrinking, as those should only touch the slot they are
    ///   currently storing to or shrinking.
    /// * `pubkeys_removed_from_accounts_index` - These keys have already been removed from the
    ///   accounts index and should not be unref'd. If they exist in the accounts index,
    ///   they are NEW.
    /// * `handle_reclaims`. `purge_stats` are stats used to track performance of purging
    ///   dead slots if value is `ProcessDeadSlots`.
    ///   Otherwise, there can be no dead slots
    ///   that happen as a result of this call, and the function will check that no slots are
    ///   cleaned up/removed via `process_dead_slots`. For instance, on store, no slots should
    ///   be cleaned up, but during the background clean accounts purges accounts from old rooted
    ///   slots, so outdated slots may be removed.
    /// * 'mark_accounts_obsolete' - Whether to mark accounts as obsolete or not. If `Yes`, then
    ///   obsolete account entry will be marked in the storage so snapshots/accounts hash can
    ///   determine the state of the account at a specified slot. This should only be done if the
    ///   account is already unrefed and removed from the accounts index
    ///   It must be unrefed and removed to avoid double counting or missed counting in shrink
    fn handle_reclaims<'a, I>(
        &'a self,
        reclaims: Option<I>,
        expected_single_dead_slot: Option<Slot>,
        pubkeys_removed_from_accounts_index: &PubkeysRemovedFromAccountsIndex,
        handle_reclaims: HandleReclaims<'a>,
        mark_accounts_obsolete: MarkAccountsObsolete,
    ) -> ReclaimResult
    where
        I: Iterator<Item = &'a (Slot, AccountInfo)>,
    {
        let mut reclaim_result = ReclaimResult::default();
        if let Some(reclaims) = reclaims {
            let (dead_slots, reclaimed_offsets) = self.remove_dead_accounts(
                reclaims,
                expected_single_dead_slot,
                mark_accounts_obsolete,
            );
            reclaim_result.1 = reclaimed_offsets;

            if let HandleReclaims::ProcessDeadSlots(purge_stats) = handle_reclaims {
                if let Some(expected_single_dead_slot) = expected_single_dead_slot {
                    assert!(dead_slots.len() <= 1);
                    if dead_slots.len() == 1 {
                        assert!(dead_slots.contains(&expected_single_dead_slot));
                    }
                }

                self.process_dead_slots(
                    &dead_slots,
                    Some(&mut reclaim_result.0),
                    purge_stats,
                    pubkeys_removed_from_accounts_index,
                );
            } else {
                assert!(dead_slots.is_empty());
            }
        }
        reclaim_result
    }

    /// During clean, some zero-lamport accounts that are marked for purge should *not* actually
    /// get purged.  Filter out those accounts here by removing them from 'candidates'.
    /// Candidates may contain entries with empty slots list in CleaningInfo.
    /// The function removes such entries from 'candidates'.
    ///
    /// When using incremental snapshots, do not purge zero-lamport accounts if the slot is higher
    /// than the latest full snapshot slot.  This is to protect against the following scenario:
    ///
    ///   ```text
    ///   A full snapshot is taken, including account 'alpha' with a non-zero balance.  In a later slot,
    ///   alpha's lamports go to zero.  Eventually, cleaning runs.  Without this change,
    ///   alpha would be cleaned up and removed completely. Finally, an incremental snapshot is taken.
    ///
    ///   Later, the incremental and full snapshots are used to rebuild the bank and accounts
    ///   database (e.x. if the node restarts).  The full snapshot _does_ contain alpha
    ///   and its balance is non-zero.  However, since alpha was cleaned up in a slot after the full
    ///   snapshot slot (due to having zero lamports), the incremental snapshot would not contain alpha.
    ///   Thus, the accounts database will contain the old, incorrect info for alpha with a non-zero
    ///   balance.  Very bad!
    ///   ```
    ///
    /// This filtering step can be skipped if there is no `latest_full_snapshot_slot`, or if the
    /// `max_clean_root_inclusive` is less-than-or-equal-to the `latest_full_snapshot_slot`.
    fn filter_zero_lamport_clean_for_incremental_snapshots(
        &self,
        max_clean_root_inclusive: Option<Slot>,
        store_counts: &HashMap<Slot, (usize, HashSet<Pubkey>)>,
        candidates: &mut [HashMap<Pubkey, CleaningInfo>],
    ) {
        let latest_full_snapshot_slot = self.latest_full_snapshot_slot();
        let should_filter_for_incremental_snapshots = max_clean_root_inclusive.unwrap_or(Slot::MAX)
            > latest_full_snapshot_slot.unwrap_or(Slot::MAX);
        assert!(
            latest_full_snapshot_slot.is_some() || !should_filter_for_incremental_snapshots,
            "if filtering for incremental snapshots, then snapshots should be enabled",
        );

        for bin in candidates {
            bin.retain(|pubkey, cleaning_info| {
                let slot_list = &cleaning_info.slot_list;
                debug_assert!(!slot_list.is_empty(), "candidate slot_list can't be empty");
                // Only keep candidates where the entire history of the account in the root set
                // can be purged. All AppendVecs for those updates are dead.
                for (slot, _account_info) in slot_list.iter() {
                    if let Some(store_count) = store_counts.get(slot) {
                        if store_count.0 != 0 {
                            // one store this pubkey is in is not being removed, so this pubkey cannot be removed at all
                            return false;
                        }
                    } else {
                        // store is not being removed, so this pubkey cannot be removed at all
                        return false;
                    }
                }

                // Exit early if not filtering more for incremental snapshots
                if !should_filter_for_incremental_snapshots {
                    return true;
                }

                // Safety: We exited early if the slot list was empty,
                // so we're guaranteed here that `.max_by_key()` returns Some.
                let (slot, account_info) = slot_list
                    .iter()
                    .max_by_key(|(slot, _account_info)| slot)
                    .unwrap();

                // Do *not* purge zero-lamport accounts if the slot is greater than the last full
                // snapshot slot.  Since we're `retain`ing the accounts-to-purge, I felt creating
                // the `cannot_purge` variable made this easier to understand.  Accounts that do
                // not get purged here are added to a list so they be considered for purging later
                // (i.e. after the next full snapshot).
                assert!(account_info.is_zero_lamport());
                let cannot_purge = *slot > latest_full_snapshot_slot.unwrap();
                if cannot_purge {
                    self.zero_lamport_accounts_to_purge_after_full_snapshot
                        .insert((*slot, *pubkey));
                }
                !cannot_purge
            });
        }
    }

    // Must be kept private!, does sensitive cleanup that should only be called from
    // supported pipelines in AccountsDb
    /// pubkeys_removed_from_accounts_index - These keys have already been removed from the accounts index
    ///    and should not be unref'd. If they exist in the accounts index, they are NEW.
    fn process_dead_slots(
        &self,
        dead_slots: &IntSet<Slot>,
        purged_account_slots: Option<&mut AccountSlots>,
        purge_stats: &PurgeStats,
        pubkeys_removed_from_accounts_index: &PubkeysRemovedFromAccountsIndex,
    ) {
        if dead_slots.is_empty() {
            return;
        }
        let mut clean_dead_slots = Measure::start("reclaims::clean_dead_slots");
        self.clean_stored_dead_slots(
            dead_slots,
            purged_account_slots,
            pubkeys_removed_from_accounts_index,
        );
        clean_dead_slots.stop();

        let mut purge_removed_slots = Measure::start("reclaims::purge_removed_slots");
        self.purge_dead_slots_from_storage(dead_slots.iter(), purge_stats);
        purge_removed_slots.stop();

        // If the slot is dead, remove the need to shrink the storages as
        // the storage entries will be purged.
        {
            let mut list = self.shrink_candidate_slots.lock().unwrap();
            for slot in dead_slots {
                list.remove(slot);
            }
        }

        debug!(
            "process_dead_slots({}): {} {} {:?}",
            dead_slots.len(),
            clean_dead_slots,
            purge_removed_slots,
            dead_slots,
        );
    }

    /// load the account index entry for the first `count` items in `accounts`
    /// store a reference to all alive accounts in `alive_accounts`
    /// store all pubkeys dead in `slot_to_shrink` in `pubkeys_to_unref`
    /// return sum of account size for all alive accounts
    fn load_accounts_index_for_shrink<'a, T: ShrinkCollectRefs<'a>>(
        &self,
        accounts: &'a [AccountFromStorage],
        stats: &ShrinkStats,
        slot_to_shrink: Slot,
    ) -> LoadAccountsIndexForShrink<'a, T> {
        let count = accounts.len();
        let mut alive_accounts = T::with_capacity(count, slot_to_shrink);
        let mut pubkeys_to_unref = Vec::with_capacity(count);
        let mut zero_lamport_single_ref_pubkeys = Vec::with_capacity(count);

        let mut alive = 0;
        let mut dead = 0;
        let mut index = 0;
        let mut index_scan_returned_some_count = 0;
        let mut index_scan_returned_none_count = 0;
        let mut all_are_zero_lamports = true;
        let latest_full_snapshot_slot = self.latest_full_snapshot_slot();
        self.accounts_index.scan(
            accounts.iter().map(|account| account.pubkey()),
            |pubkey, slots_refs, _entry| {
                let stored_account = &accounts[index];
                let mut do_populate_accounts_for_shrink = |ref_count, slot_list| {
                    if stored_account.is_zero_lamport()
                        && ref_count == 1
                        && latest_full_snapshot_slot
                            .map(|latest_full_snapshot_slot| {
                                latest_full_snapshot_slot >= slot_to_shrink
                            })
                            .unwrap_or(true)
                    {
                        // only do this if our slot is prior to the latest full snapshot
                        // we found a zero lamport account that is the only instance of this account. We can delete it completely.
                        zero_lamport_single_ref_pubkeys.push(pubkey);
                        self.add_uncleaned_pubkeys_after_shrink(
                            slot_to_shrink,
                            [*pubkey].into_iter(),
                        );
                    } else {
                        all_are_zero_lamports &= stored_account.is_zero_lamport();
                        alive_accounts.add(ref_count, stored_account, slot_list);
                        alive += 1;
                    }
                };
                if let Some((slot_list, ref_count)) = slots_refs {
                    index_scan_returned_some_count += 1;
                    let is_alive = slot_list.iter().any(|(slot, _acct_info)| {
                        // if the accounts index contains an entry at this slot, then the append vec we're asking about contains this item and thus, it is alive at this slot
                        *slot == slot_to_shrink
                    });

                    if !is_alive {
                        // This pubkey was found in the storage, but no longer exists in the index.
                        // It would have had a ref to the storage from the initial store, but it will
                        // not exist in the re-written slot. Unref it to keep the index consistent with
                        // rewriting the storage entries.
                        pubkeys_to_unref.push(pubkey);
                        dead += 1;
                    } else {
                        do_populate_accounts_for_shrink(ref_count, slot_list);
                    }
                } else {
                    index_scan_returned_none_count += 1;
                    // getting None here means the account is 'normal' and was written to disk. This means it must have ref_count=1 and
                    // slot_list.len() = 1. This means it must be alive in this slot. This is by far the most common case.
                    // Note that we could get Some(...) here if the account is in the in mem index because it is hot.
                    // Note this could also mean the account isn't on disk either. That would indicate a bug in accounts db.
                    // Account is alive.
                    let ref_count = 1;
                    let slot_list = [(slot_to_shrink, AccountInfo::default())];
                    do_populate_accounts_for_shrink(ref_count, &slot_list);
                }
                index += 1;
                AccountsIndexScanResult::OnlyKeepInMemoryIfDirty
            },
            None,
            false,
            self.scan_filter_for_shrinking,
        );
        assert_eq!(index, std::cmp::min(accounts.len(), count));
        stats
            .index_scan_returned_some
            .fetch_add(index_scan_returned_some_count, Ordering::Relaxed);
        stats
            .index_scan_returned_none
            .fetch_add(index_scan_returned_none_count, Ordering::Relaxed);
        stats.alive_accounts.fetch_add(alive, Ordering::Relaxed);
        stats.dead_accounts.fetch_add(dead, Ordering::Relaxed);

        LoadAccountsIndexForShrink {
            alive_accounts,
            pubkeys_to_unref,
            zero_lamport_single_ref_pubkeys,
            all_are_zero_lamports,
        }
    }

    /// get all accounts in all the storages passed in
    /// for duplicate pubkeys, the account with the highest write_value is returned
    pub fn get_unique_accounts_from_storage(
        &self,
        store: &AccountStorageEntry,
    ) -> GetUniqueAccountsResult {
        let capacity = store.capacity();
        let mut stored_accounts = Vec::with_capacity(store.count());
        store
            .accounts
            .scan_accounts_without_data(|offset, account| {
                // file_id is unused and can be anything. We will always be loading whatever storage is in the slot.
                let file_id = 0;
                stored_accounts.push(AccountFromStorage {
                    index_info: AccountInfo::new(
                        StorageLocation::AppendVec(file_id, offset),
                        account.is_zero_lamport(),
                    ),
                    pubkey: *account.pubkey(),
                    data_len: account.data_len as u64,
                });
            })
            .expect("must scan accounts storage");

        // sort by pubkey to keep account index lookups close
        let num_duplicated_accounts = Self::sort_and_remove_dups(&mut stored_accounts);

        GetUniqueAccountsResult {
            stored_accounts,
            capacity,
            num_duplicated_accounts,
        }
    }

    #[cfg(feature = "dev-context-only-utils")]
    pub fn set_storage_access(&mut self, storage_access: StorageAccess) {
        self.storage_access = storage_access;
    }

    /// Sort `accounts` by pubkey and removes all but the *last* of consecutive
    /// accounts in the vector with the same pubkey.
    ///
    /// Return the number of duplicated elements in the vector.
    #[cfg_attr(feature = "dev-context-only-utils", qualifiers(pub))]
    fn sort_and_remove_dups(accounts: &mut Vec<AccountFromStorage>) -> usize {
        // stable sort because we want the most recent only
        accounts.sort_by(|a, b| a.pubkey().cmp(b.pubkey()));
        let len0 = accounts.len();
        if accounts.len() > 1 {
            let mut last = 0;
            let mut curr = 1;

            while curr < accounts.len() {
                if accounts[curr].pubkey() != accounts[last].pubkey() {
                    last += 1;
                }
                accounts[last] = accounts[curr];
                curr += 1;
            }
            accounts.truncate(last + 1);
        }
        len0 - accounts.len()
    }

    pub(crate) fn get_unique_accounts_from_storage_for_shrink(
        &self,
        store: &AccountStorageEntry,
        stats: &ShrinkStats,
    ) -> GetUniqueAccountsResult {
        let (result, storage_read_elapsed_us) =
            measure_us!(self.get_unique_accounts_from_storage(store));
        stats
            .storage_read_elapsed
            .fetch_add(storage_read_elapsed_us, Ordering::Relaxed);
        stats
            .num_duplicated_accounts
            .fetch_add(result.num_duplicated_accounts as u64, Ordering::Relaxed);
        result
    }

    /// shared code for shrinking normal slots and combining into ancient append vecs
    /// note 'unique_accounts' is passed by ref so we can return references to data within it, avoiding self-references
    pub(crate) fn shrink_collect<'a: 'b, 'b, T: ShrinkCollectRefs<'b>>(
        &self,
        store: &'a AccountStorageEntry,
        unique_accounts: &'b mut GetUniqueAccountsResult,
        stats: &ShrinkStats,
    ) -> ShrinkCollect<'b, T> {
        let slot = store.slot();

        let GetUniqueAccountsResult {
            stored_accounts,
            capacity,
            num_duplicated_accounts,
        } = unique_accounts;

        let mut index_read_elapsed = Measure::start("index_read_elapsed");

        let len = stored_accounts.len();
        let alive_accounts_collect = Mutex::new(T::with_capacity(len, slot));
        let pubkeys_to_unref_collect = Mutex::new(Vec::with_capacity(len));
        let zero_lamport_single_ref_pubkeys_collect = Mutex::new(Vec::with_capacity(len));

        // Get a set of all obsolete offsets
        // Slot is not needed, as all obsolete accounts can be considered
        // dead for shrink. Zero lamport accounts are not marked obsolete
        let obsolete_offsets: IntSet<_> = store
            .get_obsolete_accounts(None)
            .into_iter()
            .map(|(offset, _)| offset)
            .collect();

        // Filter all the accounts that are marked obsolete
        let initial_len = stored_accounts.len();
        stored_accounts.retain(|account| !obsolete_offsets.contains(&account.index_info.offset()));
        let obsolete_accounts_filtered = initial_len - stored_accounts.len();

        stats
            .accounts_loaded
            .fetch_add(len as u64, Ordering::Relaxed);
        stats
            .num_duplicated_accounts
            .fetch_add(*num_duplicated_accounts as u64, Ordering::Relaxed);
        let all_are_zero_lamports_collect = Mutex::new(true);
        self.thread_pool_clean.install(|| {
            stored_accounts
                .par_chunks(SHRINK_COLLECT_CHUNK_SIZE)
                .for_each(|stored_accounts| {
                    let LoadAccountsIndexForShrink {
                        alive_accounts,
                        mut pubkeys_to_unref,
                        all_are_zero_lamports,
                        mut zero_lamport_single_ref_pubkeys,
                    } = self.load_accounts_index_for_shrink(stored_accounts, stats, slot);

                    // collect
                    alive_accounts_collect
                        .lock()
                        .unwrap()
                        .collect(alive_accounts);
                    pubkeys_to_unref_collect
                        .lock()
                        .unwrap()
                        .append(&mut pubkeys_to_unref);
                    zero_lamport_single_ref_pubkeys_collect
                        .lock()
                        .unwrap()
                        .append(&mut zero_lamport_single_ref_pubkeys);
                    if !all_are_zero_lamports {
                        *all_are_zero_lamports_collect.lock().unwrap() = false;
                    }
                });
        });

        let alive_accounts = alive_accounts_collect.into_inner().unwrap();
        let pubkeys_to_unref = pubkeys_to_unref_collect.into_inner().unwrap();
        let zero_lamport_single_ref_pubkeys = zero_lamport_single_ref_pubkeys_collect
            .into_inner()
            .unwrap();

        index_read_elapsed.stop();

        stats
            .obsolete_accounts_filtered
            .fetch_add(obsolete_accounts_filtered as u64, Ordering::Relaxed);

        stats
            .index_read_elapsed
            .fetch_add(index_read_elapsed.as_us(), Ordering::Relaxed);

        let alive_total_bytes = alive_accounts.alive_bytes();

        stats
            .accounts_removed
            .fetch_add(len - alive_accounts.len(), Ordering::Relaxed);
        stats.bytes_removed.fetch_add(
            capacity.saturating_sub(alive_total_bytes as u64),
            Ordering::Relaxed,
        );
        stats
            .bytes_written
            .fetch_add(alive_total_bytes as u64, Ordering::Relaxed);

        ShrinkCollect {
            slot,
            capacity: *capacity,
            pubkeys_to_unref,
            zero_lamport_single_ref_pubkeys,
            alive_accounts,
            alive_total_bytes,
            total_starting_accounts: len,
            all_are_zero_lamports: all_are_zero_lamports_collect.into_inner().unwrap(),
        }
    }

    /// These accounts were found during shrink of `slot` to be slot_list=[slot] and ref_count == 1 and lamports = 0.
    /// This means this slot contained the only account data for this pubkey and it is zero lamport.
    /// Thus, we did NOT treat this as an alive account, so we did NOT copy the zero lamport account to the new
    /// storage. So, the account will no longer be alive or exist at `slot`.
    /// So, first, remove the ref count since this newly shrunk storage will no longer access it.
    /// Second, remove `slot` from the index entry's slot list. If the slot list is now empty, then the
    /// pubkey can be removed completely from the index.
    /// In parallel with this code (which is running in the bg), the same pubkey could be revived and written to
    /// as part of tx processing. In that case, the slot list will contain a slot in the write cache and the
    /// index entry will NOT be deleted.
    fn remove_zero_lamport_single_ref_accounts_after_shrink(
        &self,
        zero_lamport_single_ref_pubkeys: &[&Pubkey],
        slot: Slot,
        stats: &ShrinkStats,
        do_assert: bool,
    ) {
        stats.purged_zero_lamports.fetch_add(
            zero_lamport_single_ref_pubkeys.len() as u64,
            Ordering::Relaxed,
        );

        // we have to unref before we `purge_keys_exact`. Otherwise, we could race with the foreground with tx processing
        // reviving this index entry and then we'd unref the revived version, which is a refcount bug.

        self.accounts_index.scan(
            zero_lamport_single_ref_pubkeys.iter().cloned(),
            |_pubkey, _slots_refs, _entry| AccountsIndexScanResult::Unref,
            if do_assert {
                Some(AccountsIndexScanResult::UnrefAssert0)
            } else {
                Some(AccountsIndexScanResult::UnrefLog0)
            },
            false,
            ScanFilter::All,
        );

        zero_lamport_single_ref_pubkeys.iter().for_each(|k| {
            _ = self.purge_keys_exact([&(**k, slot)].into_iter());
        });
    }

    /// common code from shrink and combine_ancient_slots
    /// get rid of all original store_ids in the slot
    pub(crate) fn remove_old_stores_shrink<'a, T: ShrinkCollectRefs<'a>>(
        &self,
        shrink_collect: &ShrinkCollect<'a, T>,
        stats: &ShrinkStats,
        shrink_in_progress: Option<ShrinkInProgress>,
        shrink_can_be_active: bool,
    ) {
        let mut time = Measure::start("remove_old_stores_shrink");

        // handle the zero lamport alive accounts before calling clean
        // We have to update the index entries for these zero lamport pubkeys before we remove the storage in `mark_dirty_dead_stores`
        // that contained the accounts.
        self.remove_zero_lamport_single_ref_accounts_after_shrink(
            &shrink_collect.zero_lamport_single_ref_pubkeys,
            shrink_collect.slot,
            stats,
            false,
        );

        // Purge old, overwritten storage entries
        // This has the side effect of dropping `shrink_in_progress`, which removes the old storage completely. The
        // index has to be correct before we drop the old storage.
        let dead_storages = self.mark_dirty_dead_stores(
            shrink_collect.slot,
            // If all accounts are zero lamports, then we want to mark the entire OLD append vec as dirty.
            // otherwise, we'll call 'add_uncleaned_pubkeys_after_shrink' just on the unref'd keys below.
            shrink_collect.all_are_zero_lamports,
            shrink_in_progress,
            shrink_can_be_active,
        );
        let dead_storages_len = dead_storages.len();

        if !shrink_collect.all_are_zero_lamports {
            self.add_uncleaned_pubkeys_after_shrink(
                shrink_collect.slot,
                shrink_collect.pubkeys_to_unref.iter().cloned().cloned(),
            );
        }

        let (_, drop_storage_entries_elapsed) = measure_us!(drop(dead_storages));
        time.stop();

        self.stats
            .dropped_stores
            .fetch_add(dead_storages_len as u64, Ordering::Relaxed);
        stats
            .drop_storage_entries_elapsed
            .fetch_add(drop_storage_entries_elapsed, Ordering::Relaxed);
        stats
            .remove_old_stores_shrink_us
            .fetch_add(time.as_us(), Ordering::Relaxed);
    }

    pub(crate) fn unref_shrunk_dead_accounts<'a>(
        &self,
        pubkeys: impl Iterator<Item = &'a Pubkey>,
        slot: Slot,
    ) {
        self.accounts_index.scan(
            pubkeys,
            |pubkey, slot_refs, _entry| {
                match slot_refs {
                    Some((slot_list, ref_count)) => {
                        // Let's handle the special case - after unref, the result is a single ref zero lamport account.
                        if slot_list.len() == 1 && ref_count == 2 {
                            if let Some((slot_alive, acct_info)) = slot_list.first() {
                                if acct_info.is_zero_lamport() && !acct_info.is_cached() {
                                    self.zero_lamport_single_ref_found(
                                        *slot_alive,
                                        acct_info.offset(),
                                    );
                                }
                            }
                        }
                    }
                    None => {
                        // We also expect that the accounts index must contain an
                        // entry for `pubkey`. Log a warning for now. In future,
                        // we will panic when this happens.
                        warn!(
                            "pubkey {pubkey} in slot {slot} was NOT found in accounts index \
                             during shrink"
                        );
                        datapoint_warn!(
                            "accounts_db-shink_pubkey_missing_from_index",
                            ("store_slot", slot, i64),
                            ("pubkey", pubkey.to_string(), String),
                        );
                    }
                }
                AccountsIndexScanResult::Unref
            },
            None,
            false,
            ScanFilter::All,
        );
    }

    /// This function handles the case when zero lamport single ref accounts are found during shrink.
    pub(crate) fn zero_lamport_single_ref_found(&self, slot: Slot, offset: Offset) {
        // This function can be called when a zero lamport single ref account is
        // found during shrink. Therefore, we can't use the safe version of
        // `get_slot_storage_entry` because shrink_in_progress map may not be
        // empty. We have to use the unsafe version to avoid to assert failure.
        // However, there is a possibility that the storage entry that we get is
        // an old one, which is being shrunk away, because multiple slots can be
        // shrunk away in parallel by thread pool. If this happens, any zero
        // lamport single ref offset marked on the storage will be lost when the
        // storage is dropped. However, this is not a problem, because after the
        // storage being shrunk, the new storage will not have any zero lamport
        // single ref account anyway. Therefore, we don't need to worry about
        // marking zero lamport single ref offset on the new storage.
        if let Some(store) = self
            .storage
            .get_slot_storage_entry_shrinking_in_progress_ok(slot)
        {
            if store.insert_zero_lamport_single_ref_account_offset(offset) {
                // this wasn't previously marked as zero lamport single ref
                self.shrink_stats
                    .num_zero_lamport_single_ref_accounts_found
                    .fetch_add(1, Ordering::Relaxed);

                if store.num_zero_lamport_single_ref_accounts() == store.count() {
                    // all accounts in this storage can be dead
                    self.dirty_stores.entry(slot).or_insert(store);
                    self.shrink_stats
                        .num_dead_slots_added_to_clean
                        .fetch_add(1, Ordering::Relaxed);
                } else if Self::is_shrinking_productive(&store)
                    && self.is_candidate_for_shrink(&store)
                {
                    // this store might be eligible for shrinking now
                    let is_new = self.shrink_candidate_slots.lock().unwrap().insert(slot);
                    if is_new {
                        self.shrink_stats
                            .num_slots_with_zero_lamport_accounts_added_to_shrink
                            .fetch_add(1, Ordering::Relaxed);
                    }
                } else {
                    self.shrink_stats
                        .marking_zero_dead_accounts_in_non_shrinkable_store
                        .fetch_add(1, Ordering::Relaxed);
                }
            }
        }
    }

    /// Shrinks `store` by rewriting the alive accounts to a new storage
    fn shrink_storage(&self, store: Arc<AccountStorageEntry>) {
        let slot = store.slot();
        if self.accounts_cache.contains(slot) {
            // It is not correct to shrink a slot while it is in the write cache until flush is complete and the slot is removed from the write cache.
            // There can exist a window after a slot is made a root and before the write cache flushing for that slot begins and then completes.
            // There can also exist a window after a slot is being flushed from the write cache until the index is updated and the slot is removed from the write cache.
            // During the second window, once an append vec has been created for the slot, it could be possible to try to shrink that slot.
            // Shrink no-ops before this function if there is no store for the slot (notice this function requires 'store' to be passed).
            // So, if we enter this function but the slot is still in the write cache, reasonable behavior is to skip shrinking this slot.
            // Flush will ONLY write alive accounts to the append vec, which is what shrink does anyway.
            // Flush then adds the slot to 'uncleaned_roots', which causes clean to take a look at the slot.
            // Clean causes us to mark accounts as dead, which causes shrink to later take a look at the slot.
            // This could be an assert, but it could lead to intermittency in tests.
            // It is 'correct' to ignore calls to shrink when a slot is still in the write cache.
            return;
        }
        let mut unique_accounts =
            self.get_unique_accounts_from_storage_for_shrink(&store, &self.shrink_stats);
        debug!("do_shrink_slot_store: slot: {slot}");
        let shrink_collect = self.shrink_collect::<AliveAccounts<'_>>(
            &store,
            &mut unique_accounts,
            &self.shrink_stats,
        );

        // This shouldn't happen if alive_bytes is accurate.
        // However, it is possible that the remaining alive bytes could be 0. In that case, the whole slot should be marked dead by clean.
        if Self::should_not_shrink(
            shrink_collect.alive_total_bytes as u64,
            shrink_collect.capacity,
        ) || shrink_collect.alive_total_bytes == 0
        {
            if shrink_collect.alive_total_bytes == 0 {
                // clean needs to take care of this dead slot
                self.dirty_stores.insert(slot, store.clone());
            }

            if !shrink_collect.all_are_zero_lamports {
                // if all are zero lamports, then we expect that we would like to mark the whole slot dead, but we cannot. That's clean's job.
                info!(
                    "Unexpected shrink for slot {} alive {} capacity {}, likely caused by a bug \
                     for calculating alive bytes.",
                    slot, shrink_collect.alive_total_bytes, shrink_collect.capacity
                );
            }

            self.shrink_stats
                .skipped_shrink
                .fetch_add(1, Ordering::Relaxed);
            return;
        }

        self.unref_shrunk_dead_accounts(shrink_collect.pubkeys_to_unref.iter().cloned(), slot);

        let total_accounts_after_shrink = shrink_collect.alive_accounts.len();
        debug!(
            "shrinking: slot: {}, accounts: ({} => {}) bytes: {} original: {}",
            slot,
            shrink_collect.total_starting_accounts,
            total_accounts_after_shrink,
            shrink_collect.alive_total_bytes,
            shrink_collect.capacity,
        );

        let mut stats_sub = ShrinkStatsSub::default();
        let mut rewrite_elapsed = Measure::start("rewrite_elapsed");
        let (shrink_in_progress, time_us) =
            measure_us!(self.get_store_for_shrink(slot, shrink_collect.alive_total_bytes as u64));
        stats_sub.create_and_insert_store_elapsed_us = Saturating(time_us);

        // here, we're writing back alive_accounts. That should be an atomic operation
        // without use of rather wide locks in this whole function, because we're
        // mutating rooted slots; There should be no writers to them.
        let accounts = [(slot, &shrink_collect.alive_accounts.alive_accounts()[..])];
        let storable_accounts = StorableAccountsBySlot::new(slot, &accounts, self);
        stats_sub.store_accounts_timing =
            self.store_accounts_frozen(storable_accounts, shrink_in_progress.new_storage());

        rewrite_elapsed.stop();
        stats_sub.rewrite_elapsed_us = Saturating(rewrite_elapsed.as_us());

        // `store_accounts_frozen()` above may have purged accounts from some
        // other storage entries (the ones that were just overwritten by this
        // new storage entry). This means some of those stores might have caused
        // this slot to be read to `self.shrink_candidate_slots`, so delete
        // those here
        self.shrink_candidate_slots.lock().unwrap().remove(&slot);

        self.remove_old_stores_shrink(
            &shrink_collect,
            &self.shrink_stats,
            Some(shrink_in_progress),
            false,
        );

        self.reopen_storage_as_readonly_shrinking_in_progress_ok(slot);

        Self::update_shrink_stats(&self.shrink_stats, stats_sub, true);
        self.shrink_stats.report();
    }

    pub(crate) fn update_shrink_stats(
        shrink_stats: &ShrinkStats,
        stats_sub: ShrinkStatsSub,
        increment_count: bool,
    ) {
        if increment_count {
            shrink_stats
                .num_slots_shrunk
                .fetch_add(1, Ordering::Relaxed);
        }
        shrink_stats.create_and_insert_store_elapsed.fetch_add(
            stats_sub.create_and_insert_store_elapsed_us.0,
            Ordering::Relaxed,
        );
        shrink_stats.store_accounts_elapsed.fetch_add(
            stats_sub.store_accounts_timing.store_accounts_elapsed,
            Ordering::Relaxed,
        );
        shrink_stats.update_index_elapsed.fetch_add(
            stats_sub.store_accounts_timing.update_index_elapsed,
            Ordering::Relaxed,
        );
        shrink_stats.handle_reclaims_elapsed.fetch_add(
            stats_sub.store_accounts_timing.handle_reclaims_elapsed,
            Ordering::Relaxed,
        );
        shrink_stats
            .rewrite_elapsed
            .fetch_add(stats_sub.rewrite_elapsed_us.0, Ordering::Relaxed);
        shrink_stats
            .unpackable_slots_count
            .fetch_add(stats_sub.unpackable_slots_count.0 as u64, Ordering::Relaxed);
        shrink_stats.newest_alive_packed_count.fetch_add(
            stats_sub.newest_alive_packed_count.0 as u64,
            Ordering::Relaxed,
        );
    }

    /// get stores for 'slot'
    /// Drop 'shrink_in_progress', which will cause the old store to be removed from the storage map.
    /// For 'shrink_in_progress'.'old_storage' which is not retained, insert in 'dead_storages' and optionally 'dirty_stores'
    /// This is the end of the life cycle of `shrink_in_progress`.
    pub fn mark_dirty_dead_stores(
        &self,
        slot: Slot,
        add_dirty_stores: bool,
        shrink_in_progress: Option<ShrinkInProgress>,
        shrink_can_be_active: bool,
    ) -> Vec<Arc<AccountStorageEntry>> {
        let mut dead_storages = Vec::default();

        let mut not_retaining_store = |store: &Arc<AccountStorageEntry>| {
            if add_dirty_stores {
                self.dirty_stores.insert(slot, store.clone());
            }
            dead_storages.push(store.clone());
        };

        if let Some(shrink_in_progress) = shrink_in_progress {
            // shrink is in progress, so 1 new append vec to keep, 1 old one to throw away
            not_retaining_store(shrink_in_progress.old_storage());
            // dropping 'shrink_in_progress' removes the old append vec that was being shrunk from db's storage
        } else if let Some(store) = self.storage.remove(&slot, shrink_can_be_active) {
            // no shrink in progress, so all append vecs in this slot are dead
            not_retaining_store(&store);
        }

        dead_storages
    }

    /// we are done writing to the storage at `slot`. It can be re-opened as read-only if that would help
    /// system performance.
    pub(crate) fn reopen_storage_as_readonly_shrinking_in_progress_ok(&self, slot: Slot) {
        if let Some(storage) = self
            .storage
            .get_slot_storage_entry_shrinking_in_progress_ok(slot)
        {
            if let Some(new_storage) = storage.reopen_as_readonly(self.storage_access) {
                // consider here the race condition of tx processing having looked up something in the index,
                // which could return (slot, append vec id). We want the lookup for the storage to get a storage
                // that works whether the lookup occurs before or after the replace call here.
                // So, the two storages have to be exactly equivalent wrt offsets, counts, len, id, etc.
                assert_eq!(storage.id(), new_storage.id());
                assert_eq!(storage.accounts.len(), new_storage.accounts.len());
                self.storage
                    .replace_storage_with_equivalent(slot, Arc::new(new_storage));
            }
        }
    }

    /// return a store that can contain 'size' bytes
    pub fn get_store_for_shrink(&self, slot: Slot, size: u64) -> ShrinkInProgress<'_> {
        let shrunken_store = self.create_store(slot, size, "shrink", self.shrink_paths.as_slice());
        self.storage.shrinking_in_progress(slot, shrunken_store)
    }

    // Reads all accounts in given slot's AppendVecs and filter only to alive,
    // then create a minimum AppendVec filled with the alive.
    fn shrink_slot_forced(&self, slot: Slot) {
        debug!("shrink_slot_forced: slot: {slot}");

        if let Some(store) = self
            .storage
            .get_slot_storage_entry_shrinking_in_progress_ok(slot)
        {
            if Self::is_shrinking_productive(&store) {
                self.shrink_storage(store)
            }
        }
    }

    fn all_slots_in_storage(&self) -> Vec<Slot> {
        self.storage.all_slots()
    }

    /// Given the input `ShrinkCandidates`, this function sorts the stores by their alive ratio
    /// in increasing order with the most sparse entries in the front. It will then simulate the
    /// shrinking by working on the most sparse entries first and if the overall alive ratio is
    /// achieved, it will stop and return:
    /// first tuple element: the filtered-down candidates and
    /// second duple element: the candidates which
    /// are skipped in this round and might be eligible for the future shrink.
    fn select_candidates_by_total_usage(
        &self,
        shrink_slots: &ShrinkCandidates,
        shrink_ratio: f64,
    ) -> (IntMap<Slot, Arc<AccountStorageEntry>>, ShrinkCandidates) {
        struct StoreUsageInfo {
            slot: Slot,
            alive_ratio: f64,
            store: Arc<AccountStorageEntry>,
        }
        let mut store_usage: Vec<StoreUsageInfo> = Vec::with_capacity(shrink_slots.len());
        let mut total_alive_bytes: u64 = 0;
        let mut total_bytes: u64 = 0;
        for slot in shrink_slots {
            let Some(store) = self.storage.get_slot_storage_entry(*slot) else {
                continue;
            };
            let alive_bytes = store.alive_bytes();
            total_alive_bytes += alive_bytes as u64;
            total_bytes += store.capacity();
            let alive_ratio = alive_bytes as f64 / store.capacity() as f64;
            store_usage.push(StoreUsageInfo {
                slot: *slot,
                alive_ratio,
                store: store.clone(),
            });
        }
        store_usage.sort_by(|a, b| {
            a.alive_ratio
                .partial_cmp(&b.alive_ratio)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // Working from the beginning of store_usage which are the most sparse and see when we can stop
        // shrinking while still achieving the overall goals.
        let mut shrink_slots = IntMap::default();
        let mut shrink_slots_next_batch = ShrinkCandidates::default();
        for usage in &store_usage {
            let store = &usage.store;
            let alive_ratio = (total_alive_bytes as f64) / (total_bytes as f64);
            debug!(
                "alive_ratio: {:?} store_id: {:?}, store_ratio: {:?} requirement: {:?}, \
                 total_bytes: {:?} total_alive_bytes: {:?}",
                alive_ratio,
                usage.store.id(),
                usage.alive_ratio,
                shrink_ratio,
                total_bytes,
                total_alive_bytes
            );
            if alive_ratio > shrink_ratio {
                // we have reached our goal, stop
                debug!(
                    "Shrinking goal can be achieved at slot {:?}, total_alive_bytes: {:?} \
                     total_bytes: {:?}, alive_ratio: {:}, shrink_ratio: {:?}",
                    usage.slot, total_alive_bytes, total_bytes, alive_ratio, shrink_ratio
                );
                if usage.alive_ratio < shrink_ratio {
                    shrink_slots_next_batch.insert(usage.slot);
                } else {
                    break;
                }
            } else {
                let current_store_size = store.capacity();
                let after_shrink_size = store.alive_bytes() as u64;
                let bytes_saved = current_store_size.saturating_sub(after_shrink_size);
                total_bytes -= bytes_saved;
                shrink_slots.insert(usage.slot, Arc::clone(store));
            }
        }
        (shrink_slots, shrink_slots_next_batch)
    }

    fn get_roots_less_than(&self, slot: Slot) -> Vec<Slot> {
        self.accounts_index
            .roots_tracker
            .read()
            .unwrap()
            .alive_roots
            .get_all_less_than(slot)
    }

    /// return all slots that are more than one epoch old and thus could already be an ancient append vec
    /// or which could need to be combined into a new or existing ancient append vec
    /// offset is used to combine newer slots than we normally would. This is designed to be used for testing.
    fn get_sorted_potential_ancient_slots(&self, oldest_non_ancient_slot: Slot) -> Vec<Slot> {
        let mut ancient_slots = self.get_roots_less_than(oldest_non_ancient_slot);
        ancient_slots.sort_unstable();
        ancient_slots
    }

    /// get a sorted list of slots older than an epoch
    /// squash those slots into ancient append vecs
    pub fn shrink_ancient_slots(&self, epoch_schedule: &EpochSchedule) {
        if self.ancient_append_vec_offset.is_none() {
            return;
        }

        let oldest_non_ancient_slot = self.get_oldest_non_ancient_slot(epoch_schedule);
        let can_randomly_shrink = true;
        let sorted_slots = self.get_sorted_potential_ancient_slots(oldest_non_ancient_slot);
        self.combine_ancient_slots_packed(sorted_slots, can_randomly_shrink);
    }

    /// each slot in 'dropped_roots' has been combined into an ancient append vec.
    /// We are done with the slot now forever.
    pub(crate) fn handle_dropped_roots_for_ancient(
        &self,
        dropped_roots: impl Iterator<Item = Slot>,
    ) {
        let mut accounts_delta_hashes = self.accounts_delta_hashes.lock().unwrap();

        dropped_roots.for_each(|slot| {
            self.accounts_index.clean_dead_slot(slot);
            accounts_delta_hashes.remove(&slot);
            // the storage has been removed from this slot and recycled or dropped
            assert!(self.storage.remove(&slot, false).is_none());
            debug_assert!(
                !self
                    .accounts_index
                    .roots_tracker
                    .read()
                    .unwrap()
                    .alive_roots
                    .contains(&slot),
                "slot: {slot}"
            );
        });
    }

    /// add all 'pubkeys' into the set of pubkeys that are 'uncleaned', associated with 'slot'
    /// clean will visit these pubkeys next time it runs
    fn add_uncleaned_pubkeys_after_shrink(
        &self,
        slot: Slot,
        pubkeys: impl Iterator<Item = Pubkey>,
    ) {
        /*
        This is only called during 'shrink'-type operations.
        Original accounts were separated into 'accounts' and 'pubkeys_to_unref'.
        These sets correspond to 'alive' and 'dead'.
        'alive' means this account in this slot is in the accounts index.
        'dead' means this account in this slot is NOT in the accounts index.
        If dead, nobody will care if this version of this account is not written into the newly shrunk append vec for this slot.
        For all dead accounts, they were already unrefed and are now absent in the new append vec.
        This means that another version of this pubkey could possibly now be cleaned since this one is now gone.
        For example, a zero lamport account in a later slot can be removed if we just removed the only non-zero lamport account for that pubkey in this slot.
        So, for all unrefed accounts, send them to clean to be revisited next time clean runs.
        If an account is alive, then its status has not changed. It was previously alive in this slot. It is still alive in this slot.
        Clean doesn't care about alive accounts that remain alive.
        Except... A slightly different case is if ALL the alive accounts in this slot are zero lamport accounts, then it is possible that
        this slot can be marked dead. So, if all alive accounts are zero lamports, we send the entire OLD/pre-shrunk append vec
        to clean so that all the pubkeys are visited.
        It is a performance optimization to not send the ENTIRE old/pre-shrunk append vec to clean in the normal case.
        */

        let mut uncleaned_pubkeys = self.uncleaned_pubkeys.entry(slot).or_default();
        uncleaned_pubkeys.extend(pubkeys);
    }

    pub fn shrink_candidate_slots(&self, epoch_schedule: &EpochSchedule) -> usize {
        let oldest_non_ancient_slot = self.get_oldest_non_ancient_slot(epoch_schedule);

        let shrink_candidates_slots =
            std::mem::take(&mut *self.shrink_candidate_slots.lock().unwrap());
        self.shrink_stats
            .initial_candidates_count
            .store(shrink_candidates_slots.len() as u64, Ordering::Relaxed);

        let candidates_count = shrink_candidates_slots.len();
        let ((mut shrink_slots, shrink_slots_next_batch), select_time_us) = measure_us!({
            if let AccountShrinkThreshold::TotalSpace { shrink_ratio } = self.shrink_ratio {
                let (shrink_slots, shrink_slots_next_batch) =
                    self.select_candidates_by_total_usage(&shrink_candidates_slots, shrink_ratio);
                (shrink_slots, Some(shrink_slots_next_batch))
            } else {
                (
                    // lookup storage for each slot
                    shrink_candidates_slots
                        .into_iter()
                        .filter_map(|slot| {
                            self.storage
                                .get_slot_storage_entry(slot)
                                .map(|storage| (slot, storage))
                        })
                        .collect(),
                    None,
                )
            }
        });

        // If there are too few slots to shrink, add an ancient slot
        // for shrinking.
        if shrink_slots.len() < SHRINK_INSERT_ANCIENT_THRESHOLD {
            let mut ancients = self.best_ancient_slots_to_shrink.write().unwrap();
            while let Some((slot, capacity)) = ancients.pop_front() {
                if let Some(store) = self.storage.get_slot_storage_entry(slot) {
                    if !shrink_slots.contains(&slot)
                        && capacity == store.capacity()
                        && Self::is_candidate_for_shrink(self, &store)
                    {
                        let ancient_bytes_added_to_shrink = store.alive_bytes() as u64;
                        shrink_slots.insert(slot, store);
                        self.shrink_stats
                            .ancient_bytes_added_to_shrink
                            .fetch_add(ancient_bytes_added_to_shrink, Ordering::Relaxed);
                        self.shrink_stats
                            .ancient_slots_added_to_shrink
                            .fetch_add(1, Ordering::Relaxed);
                        break;
                    }
                }
            }
        }
        if shrink_slots.is_empty()
            && shrink_slots_next_batch
                .as_ref()
                .map(|s| s.is_empty())
                .unwrap_or(true)
        {
            return 0;
        }

        let _guard = (!shrink_slots.is_empty())
            .then_some(|| self.active_stats.activate(ActiveStatItem::Shrink));

        let num_selected = shrink_slots.len();
        let (_, shrink_all_us) = measure_us!({
            self.thread_pool_clean.install(|| {
                shrink_slots
                    .into_par_iter()
                    .for_each(|(slot, slot_shrink_candidate)| {
                        if self.ancient_append_vec_offset.is_some()
                            && slot < oldest_non_ancient_slot
                        {
                            self.shrink_stats
                                .num_ancient_slots_shrunk
                                .fetch_add(1, Ordering::Relaxed);
                        }
                        self.shrink_storage(slot_shrink_candidate);
                    });
            })
        });

        let mut pended_counts: usize = 0;
        if let Some(shrink_slots_next_batch) = shrink_slots_next_batch {
            let mut shrink_slots = self.shrink_candidate_slots.lock().unwrap();
            pended_counts = shrink_slots_next_batch.len();
            for slot in shrink_slots_next_batch {
                shrink_slots.insert(slot);
            }
        }

        datapoint_info!(
            "shrink_candidate_slots",
            ("select_time_us", select_time_us, i64),
            ("shrink_all_us", shrink_all_us, i64),
            ("candidates_count", candidates_count, i64),
            ("selected_count", num_selected, i64),
            ("deferred_to_next_round_count", pended_counts, i64)
        );

        num_selected
    }

    /// This is only called at startup from bank when we are being extra careful such as when we downloaded a snapshot.
    /// Also called from tests.
    /// `newest_slot_skip_shrink_inclusive` is used to avoid shrinking the slot we are loading a snapshot from. If we shrink that slot, we affect
    /// the bank hash calculation verification at startup.
    pub fn shrink_all_slots(
        &self,
        is_startup: bool,
        epoch_schedule: &EpochSchedule,
        newest_slot_skip_shrink_inclusive: Option<Slot>,
    ) {
        let _guard = self.active_stats.activate(ActiveStatItem::Shrink);
        const DIRTY_STORES_CLEANING_THRESHOLD: usize = 10_000;
        const OUTER_CHUNK_SIZE: usize = 2000;
        let mut slots = self.all_slots_in_storage();
        if let Some(newest_slot_skip_shrink_inclusive) = newest_slot_skip_shrink_inclusive {
            // at startup, we cannot shrink the slot that we're about to replay and recalculate bank hash for.
            // That storage's contents are used to verify the bank hash (and accounts delta hash) of the startup slot.
            slots.retain(|slot| slot < &newest_slot_skip_shrink_inclusive);
        }

        // if we are restoring from incremental + full snapshot, then we cannot clean past latest_full_snapshot_slot.
        // If we were to clean past that, then we could mark accounts prior to latest_full_snapshot_slot as dead.
        // If we mark accounts prior to latest_full_snapshot_slot as dead, then we could shrink those accounts away.
        // If we shrink accounts away, then when we run the full hash of all accounts calculation up to latest_full_snapshot_slot,
        // then we will get the wrong answer, because some accounts may be GONE from the slot range up to latest_full_snapshot_slot.
        // So, we can only clean UP TO and including latest_full_snapshot_slot.
        // As long as we don't mark anything as dead at slots > latest_full_snapshot_slot, then shrink will have nothing to do for
        // slots > latest_full_snapshot_slot.
        let maybe_clean = || {
            if self.dirty_stores.len() > DIRTY_STORES_CLEANING_THRESHOLD {
                let latest_full_snapshot_slot = self.latest_full_snapshot_slot();
                self.clean_accounts(latest_full_snapshot_slot, is_startup, epoch_schedule);
            }
        };

        if is_startup {
            let threads = num_cpus::get();
            let inner_chunk_size = std::cmp::max(OUTER_CHUNK_SIZE / threads, 1);
            slots.chunks(OUTER_CHUNK_SIZE).for_each(|chunk| {
                chunk.par_chunks(inner_chunk_size).for_each(|slots| {
                    for slot in slots {
                        self.shrink_slot_forced(*slot);
                    }
                });
                maybe_clean();
            });
        } else {
            for slot in slots {
                self.shrink_slot_forced(slot);
                maybe_clean();
            }
        }
    }

    pub fn scan_accounts<F>(
        &self,
        ancestors: &Ancestors,
        bank_id: BankId,
        mut scan_func: F,
        config: &ScanConfig,
    ) -> ScanResult<()>
    where
        F: FnMut(Option<(&Pubkey, AccountSharedData, Slot)>),
    {
        // This can error out if the slots being scanned over are aborted
        self.accounts_index.scan_accounts(
            ancestors,
            bank_id,
            |pubkey, (account_info, slot)| {
                let mut account_accessor =
                    self.get_account_accessor(slot, pubkey, &account_info.storage_location());

                let account_slot = match account_accessor {
                    LoadedAccountAccessor::Cached(None) => None,
                    _ => account_accessor.get_loaded_account(|loaded_account| {
                        (pubkey, loaded_account.take_account(), slot)
                    }),
                };
                scan_func(account_slot)
            },
            config,
        )?;

        Ok(())
    }

    #[cfg(feature = "dev-context-only-utils")]
    pub fn unchecked_scan_accounts<F>(
        &self,
        metric_name: &'static str,
        ancestors: &Ancestors,
        mut scan_func: F,
        config: &ScanConfig,
    ) where
        F: FnMut(&Pubkey, LoadedAccount, Slot),
    {
        self.accounts_index.unchecked_scan_accounts(
            metric_name,
            ancestors,
            |pubkey, (account_info, slot)| {
                self.get_account_accessor(slot, pubkey, &account_info.storage_location())
                    .get_loaded_account(|loaded_account| {
                        scan_func(pubkey, loaded_account, slot);
                    });
            },
            config,
        );
    }

    pub fn index_scan_accounts<F>(
        &self,
        ancestors: &Ancestors,
        bank_id: BankId,
        index_key: IndexKey,
        mut scan_func: F,
        config: &ScanConfig,
    ) -> ScanResult<bool>
    where
        F: FnMut(Option<(&Pubkey, AccountSharedData, Slot)>),
    {
        let key = match &index_key {
            IndexKey::ProgramId(key) => key,
            IndexKey::SplTokenMint(key) => key,
            IndexKey::SplTokenOwner(key) => key,
        };
        if !self.account_indexes.include_key(key) {
            // the requested key was not indexed in the secondary index, so do a normal scan
            let used_index = false;
            self.scan_accounts(ancestors, bank_id, scan_func, config)?;
            return Ok(used_index);
        }

        self.accounts_index.index_scan_accounts(
            ancestors,
            bank_id,
            index_key,
            |pubkey, (account_info, slot)| {
                let account_slot = self
                    .get_account_accessor(slot, pubkey, &account_info.storage_location())
                    .get_loaded_account(|loaded_account| {
                        (pubkey, loaded_account.take_account(), slot)
                    });
                scan_func(account_slot)
            },
            config,
        )?;
        let used_index = true;
        Ok(used_index)
    }

    /// Scan a specific slot through all the account storage
    pub(crate) fn scan_account_storage<R, B>(
        &self,
        slot: Slot,
        cache_map_func: impl Fn(&LoadedAccount) -> Option<R> + Sync,
        storage_scan_func: impl for<'a, 'b, 'storage> Fn(
                &'b mut B,
                &'a StoredAccountInfoWithoutData<'storage>,
                Option<&'storage [u8]>, // account data
            ) + Sync,
        scan_account_storage_data: ScanAccountStorageData,
    ) -> ScanStorageResult<R, B>
    where
        R: Send,
        B: Send + Default + Sync,
    {
        self.scan_cache_storage_fallback(slot, cache_map_func, |retval, storage| {
            match scan_account_storage_data {
                ScanAccountStorageData::NoData => {
                    storage.scan_accounts_without_data(|_offset, account_without_data| {
                        storage_scan_func(retval, &account_without_data, None);
                    })
                }
                ScanAccountStorageData::DataRefForStorage => {
                    storage.scan_accounts(|_offset, account| {
                        let account_without_data = StoredAccountInfoWithoutData::new_from(&account);
                        storage_scan_func(retval, &account_without_data, Some(account.data));
                    })
                }
            }
            .expect("must scan accounts storage");
        })
    }

    /// Scan the cache with a fallback to storage for a specific slot.
    pub fn scan_cache_storage_fallback<R, B>(
        &self,
        slot: Slot,
        cache_map_func: impl Fn(&LoadedAccount) -> Option<R> + Sync,
        storage_fallback_func: impl Fn(&mut B, &AccountsFile) + Sync,
    ) -> ScanStorageResult<R, B>
    where
        R: Send,
        B: Send + Default + Sync,
    {
        if let Some(slot_cache) = self.accounts_cache.slot_cache(slot) {
            // If we see the slot in the cache, then all the account information
            // is in this cached slot
            if slot_cache.len() > SCAN_SLOT_PAR_ITER_THRESHOLD {
                ScanStorageResult::Cached(self.thread_pool.install(|| {
                    slot_cache
                        .par_iter()
                        .filter_map(|cached_account| {
                            cache_map_func(&LoadedAccount::Cached(Cow::Borrowed(
                                cached_account.value(),
                            )))
                        })
                        .collect()
                }))
            } else {
                ScanStorageResult::Cached(
                    slot_cache
                        .iter()
                        .filter_map(|cached_account| {
                            cache_map_func(&LoadedAccount::Cached(Cow::Borrowed(
                                cached_account.value(),
                            )))
                        })
                        .collect(),
                )
            }
        } else {
            let mut retval = B::default();
            // If the slot is not in the cache, then all the account information must have
            // been flushed. This is guaranteed because we only remove the rooted slot from
            // the cache *after* we've finished flushing in `flush_slot_cache`.
            // Regarding `shrinking_in_progress_ok`:
            // This fn could be running in the foreground, so shrinking could be running in the background, independently.
            // Even if shrinking is running, there will be 0-1 active storages to scan here at any point.
            // When a concurrent shrink completes, the active storage at this slot will
            // be replaced with an equivalent storage with only alive accounts in it.
            // A shrink on this slot could have completed anytime before the call here, a shrink could currently be in progress,
            // or the shrink could complete immediately or anytime after this call. This has always been true.
            // So, whether we get a never-shrunk, an about-to-be shrunk, or a will-be-shrunk-in-future storage here to scan,
            // all are correct and possible in a normally running system.
            if let Some(storage) = self
                .storage
                .get_slot_storage_entry_shrinking_in_progress_ok(slot)
            {
                storage_fallback_func(&mut retval, &storage.accounts);
            }

            ScanStorageResult::Stored(retval)
        }
    }

    pub fn load(
        &self,
        ancestors: &Ancestors,
        pubkey: &Pubkey,
        load_hint: LoadHint,
    ) -> Option<(AccountSharedData, Slot)> {
        self.do_load(ancestors, pubkey, None, load_hint, LoadZeroLamports::None)
    }

    /// Return Ok(index_of_matching_owner) if the account owner at `offset` is one of the pubkeys in `owners`.
    /// Return Err(MatchAccountOwnerError::NoMatch) if the account has 0 lamports or the owner is not one of
    /// the pubkeys in `owners`.
    /// Return Err(MatchAccountOwnerError::UnableToLoad) if the account could not be accessed.
    pub fn account_matches_owners(
        &self,
        ancestors: &Ancestors,
        account: &Pubkey,
        owners: &[Pubkey],
    ) -> Result<usize, MatchAccountOwnerError> {
        let (slot, storage_location, _maybe_account_accesor) = self
            .read_index_for_accessor_or_load_slow(ancestors, account, None, false)
            .ok_or(MatchAccountOwnerError::UnableToLoad)?;

        if !storage_location.is_cached() {
            let result = self.read_only_accounts_cache.load(*account, slot);
            if let Some(account) = result {
                return if account.is_zero_lamport() {
                    Err(MatchAccountOwnerError::NoMatch)
                } else {
                    owners
                        .iter()
                        .position(|entry| account.owner() == entry)
                        .ok_or(MatchAccountOwnerError::NoMatch)
                };
            }
        }

        let (account_accessor, _slot) = self
            .retry_to_get_account_accessor(
                slot,
                storage_location,
                ancestors,
                account,
                None,
                LoadHint::Unspecified,
            )
            .ok_or(MatchAccountOwnerError::UnableToLoad)?;
        account_accessor.account_matches_owners(owners)
    }

    /// load the account with `pubkey` into the read only accounts cache.
    /// The goal is to make subsequent loads (which caller expects to occur) to find the account quickly.
    pub fn load_account_into_read_cache(&self, ancestors: &Ancestors, pubkey: &Pubkey) {
        self.do_load_with_populate_read_cache(
            ancestors,
            pubkey,
            None,
            LoadHint::Unspecified,
            true,
            // no return from this function, so irrelevant
            LoadZeroLamports::None,
        );
    }

    /// note this returns None for accounts with zero lamports
    pub fn load_with_fixed_root(
        &self,
        ancestors: &Ancestors,
        pubkey: &Pubkey,
    ) -> Option<(AccountSharedData, Slot)> {
        self.load(ancestors, pubkey, LoadHint::FixedMaxRoot)
    }

    fn read_index_for_accessor_or_load_slow<'a>(
        &'a self,
        ancestors: &Ancestors,
        pubkey: &'a Pubkey,
        max_root: Option<Slot>,
        clone_in_lock: bool,
    ) -> Option<(Slot, StorageLocation, Option<LoadedAccountAccessor<'a>>)> {
        self.accounts_index.get_with_and_then(
            pubkey,
            Some(ancestors),
            max_root,
            true,
            |(slot, account_info)| {
                let storage_location = account_info.storage_location();
                let account_accessor = clone_in_lock
                    .then(|| self.get_account_accessor(slot, pubkey, &storage_location));
                (slot, storage_location, account_accessor)
            },
        )
    }

    fn retry_to_get_account_accessor<'a>(
        &'a self,
        mut slot: Slot,
        mut storage_location: StorageLocation,
        ancestors: &'a Ancestors,
        pubkey: &'a Pubkey,
        max_root: Option<Slot>,
        load_hint: LoadHint,
    ) -> Option<(LoadedAccountAccessor<'a>, Slot)> {
        // Happy drawing time! :)
        //
        // Reader                               | Accessed data source for cached/stored
        // -------------------------------------+----------------------------------
        // R1 read_index_for_accessor_or_load_slow()| cached/stored: index
        //          |                           |
        //        <(store_id, offset, ..)>      |
        //          V                           |
        // R2 retry_to_get_account_accessor()/  | cached: map of caches & entry for (slot, pubkey)
        //        get_account_accessor()        | stored: map of stores
        //          |                           |
        //        <Accessor>                    |
        //          V                           |
        // R3 check_and_get_loaded_account()/   | cached: N/A (note: basically noop unwrap)
        //        get_loaded_account()          | stored: store's entry for slot
        //          |                           |
        //        <LoadedAccount>               |
        //          V                           |
        // R4 take_account()                    | cached/stored: entry of cache/storage for (slot, pubkey)
        //          |                           |
        //        <AccountSharedData>           |
        //          V                           |
        //    Account!!                         V
        //
        // Flusher                              | Accessed data source for cached/stored
        // -------------------------------------+----------------------------------
        // F1 flush_slot_cache()                | N/A
        //          |                           |
        //          V                           |
        // F2 store_accounts_frozen()/          | map of stores (creates new entry)
        //        write_accounts_to_storage()   |
        //          |                           |
        //          V                           |
        // F3 store_accounts_frozen()/          | index
        //        update_index()                | (replaces existing store_id, offset in caches)
        //          |                           |
        //          V                           |
        // F4 accounts_cache.remove_slot()      | map of caches (removes old entry)
        //                                      V
        //
        // Remarks for flusher: So, for any reading operations, it's a race condition where F4 happens
        // between R1 and R2. In that case, retrying from R1 is safu because F3 should have
        // been occurred.
        //
        // Shrinker                             | Accessed data source for stored
        // -------------------------------------+----------------------------------
        // S1 do_shrink_slot_store()            | N/A
        //          |                           |
        //          V                           |
        // S2 store_accounts_frozen()/          | map of stores (creates new entry)
        //        write_accounts_to_storage()   |
        //          |                           |
        //          V                           |
        // S3 store_accounts_frozen()/          | index
        //        update_index()                | (replaces existing store_id, offset in stores)
        //          |                           |
        //          V                           |
        // S4 do_shrink_slot_store()/           | map of stores (removes old entry)
        //        dead_storages
        //
        // Remarks for shrinker: So, for any reading operations, it's a race condition
        // where S4 happens between R1 and R2. In that case, retrying from R1 is safu because S3 should have
        // been occurred, and S3 atomically replaced the index accordingly.
        //
        // Cleaner                              | Accessed data source for stored
        // -------------------------------------+----------------------------------
        // C1 clean_accounts()                  | N/A
        //          |                           |
        //          V                           |
        // C2 clean_accounts()/                 | index
        //        purge_keys_exact()            | (removes existing store_id, offset for stores)
        //          |                           |
        //          V                           |
        // C3 clean_accounts()/                 | map of stores (removes old entry)
        //        handle_reclaims()             |
        //
        // Remarks for cleaner: So, for any reading operations, it's a race condition
        // where C3 happens between R1 and R2. In that case, retrying from R1 is safu.
        // In that case, None would be returned while bailing out at R1.
        //
        // Purger                                 | Accessed data source for cached/stored
        // ---------------------------------------+----------------------------------
        // P1 purge_slot()                        | N/A
        //          |                             |
        //          V                             |
        // P2 purge_slots_from_cache_and_store()  | map of caches/stores (removes old entry)
        //          |                             |
        //          V                             |
        // P3 purge_slots_from_cache_and_store()/ | index
        //       purge_slot_cache()/              |
        //          purge_slot_cache_pubkeys()    | (removes existing store_id, offset for cache)
        //       purge_slot_storage()/            |
        //          purge_keys_exact()            | (removes accounts index entries)
        //          handle_reclaims()             | (removes storage entries)
        //      OR                                |
        //    clean_accounts()/                   |
        //        clean_accounts_older_than_root()| (removes existing store_id, offset for stores)
        //                                        V
        //
        // Remarks for purger: So, for any reading operations, it's a race condition
        // where P2 happens between R1 and R2. In that case, retrying from R1 is safu.
        // In that case, we may bail at index read retry when P3 hasn't been run

        #[cfg(test)]
        {
            // Give some time for cache flushing to occur here for unit tests
            sleep(Duration::from_millis(self.load_delay));
        }

        // Failsafe for potential race conditions with other subsystems
        let mut num_acceptable_failed_iterations = 0;
        loop {
            let account_accessor = self.get_account_accessor(slot, pubkey, &storage_location);
            match account_accessor {
                LoadedAccountAccessor::Cached(Some(_)) | LoadedAccountAccessor::Stored(Some(_)) => {
                    // Great! There was no race, just return :) This is the most usual situation
                    return Some((account_accessor, slot));
                }
                LoadedAccountAccessor::Cached(None) => {
                    num_acceptable_failed_iterations += 1;
                    // Cache was flushed in between checking the index and retrieving from the cache,
                    // so retry. This works because in accounts cache flush, an account is written to
                    // storage *before* it is removed from the cache
                    match load_hint {
                        LoadHint::FixedMaxRootDoNotPopulateReadCache | LoadHint::FixedMaxRoot => {
                            // it's impossible for this to fail for transaction loads from
                            // replaying/banking more than once.
                            // This is because:
                            // 1) For a slot `X` that's being replayed, there is only one
                            // latest ancestor containing the latest update for the account, and this
                            // ancestor can only be flushed once.
                            // 2) The root cannot move while replaying, so the index cannot continually
                            // find more up to date entries than the current `slot`
                            assert!(num_acceptable_failed_iterations <= 1);
                        }
                        LoadHint::Unspecified => {
                            // Because newer root can be added to the index (= not fixed),
                            // multiple flush race conditions can be observed under very rare
                            // condition, at least theoretically
                        }
                    }
                }
                LoadedAccountAccessor::Stored(None) => {
                    match load_hint {
                        LoadHint::FixedMaxRootDoNotPopulateReadCache | LoadHint::FixedMaxRoot => {
                            // When running replay on the validator, or banking stage on the leader,
                            // it should be very rare that the storage entry doesn't exist if the
                            // entry in the accounts index is the latest version of this account.
                            //
                            // There are only a few places where the storage entry may not exist
                            // after reading the index:
                            // 1) Shrink has removed the old storage entry and rewritten to
                            // a newer storage entry
                            // 2) The `pubkey` asked for in this function is a zero-lamport account,
                            // and the storage entry holding this account qualified for zero-lamport clean.
                            //
                            // In both these cases, it should be safe to retry and recheck the accounts
                            // index indefinitely, without incrementing num_acceptable_failed_iterations.
                            // That's because if the root is fixed, there should be a bounded number
                            // of pending cleans/shrinks (depends how far behind the AccountsBackgroundService
                            // is), termination to the desired condition is guaranteed.
                            //
                            // Also note that in both cases, if we do find the storage entry,
                            // we can guarantee that the storage entry is safe to read from because
                            // we grabbed a reference to the storage entry while it was still in the
                            // storage map. This means even if the storage entry is removed from the storage
                            // map after we grabbed the storage entry, the recycler should not reset the
                            // storage entry until we drop the reference to the storage entry.
                            //
                            // eh, no code in this arm? yes!
                        }
                        LoadHint::Unspecified => {
                            // RPC get_account() may have fetched an old root from the index that was
                            // either:
                            // 1) Cleaned up by clean_accounts(), so the accounts index has been updated
                            // and the storage entries have been removed.
                            // 2) Dropped by purge_slots() because the slot was on a minor fork, which
                            // removes the slots' storage entries but doesn't purge from the accounts index
                            // (account index cleanup is left to clean for stored slots). Note that
                            // this generally is impossible to occur in the wild because the RPC
                            // should hold the slot's bank, preventing it from being purged() to
                            // begin with.
                            num_acceptable_failed_iterations += 1;
                        }
                    }
                }
            }
            #[cfg(not(test))]
            let load_limit = ABSURD_CONSECUTIVE_FAILED_ITERATIONS;

            #[cfg(test)]
            let load_limit = self.load_limit.load(Ordering::Relaxed);

            let fallback_to_slow_path = if num_acceptable_failed_iterations >= load_limit {
                // The latest version of the account existed in the index, but could not be
                // fetched from storage. This means a race occurred between this function and clean
                // accounts/purge_slots
                let message = format!(
                    "do_load() failed to get key: {pubkey} from storage, latest attempt was for \
                     slot: {slot}, storage_location: {storage_location:?}, load_hint: \
                     {load_hint:?}",
                );
                datapoint_warn!("accounts_db-do_load_warn", ("warn", message, String));
                true
            } else {
                false
            };

            // Because reading from the cache/storage failed, retry from the index read
            let (new_slot, new_storage_location, maybe_account_accessor) = self
                .read_index_for_accessor_or_load_slow(
                    ancestors,
                    pubkey,
                    max_root,
                    fallback_to_slow_path,
                )?;
            // Notice the subtle `?` at previous line, we bail out pretty early if missing.

            if new_slot == slot && new_storage_location.is_store_id_equal(&storage_location) {
                let message = format!(
                    "Bad index entry detected ({}, {}, {:?}, {:?}, {:?}, {:?})",
                    pubkey,
                    slot,
                    storage_location,
                    load_hint,
                    new_storage_location,
                    self.accounts_index.get_cloned(pubkey)
                );
                // Considering that we've failed to get accessor above and further that
                // the index still returned the same (slot, store_id) tuple, offset must be same
                // too.
                assert!(
                    new_storage_location.is_offset_equal(&storage_location),
                    "{message}"
                );

                // If the entry was missing from the cache, that means it must have been flushed,
                // and the accounts index is always updated before cache flush, so store_id must
                // not indicate being cached at this point.
                assert!(!new_storage_location.is_cached(), "{message}");

                // If this is not a cache entry, then this was a minor fork slot
                // that had its storage entries cleaned up by purge_slots() but hasn't been
                // cleaned yet. That means this must be rpc access and not replay/banking at the
                // very least. Note that purge shouldn't occur even for RPC as caller must hold all
                // of ancestor slots..
                assert_eq!(load_hint, LoadHint::Unspecified, "{message}");

                // Everything being assert!()-ed, let's panic!() here as it's an error condition
                // after all....
                // That reasoning is based on the fact all of code-path reaching this fn
                // retry_to_get_account_accessor() must outlive the Arc<Bank> (and its all
                // ancestors) over this fn invocation, guaranteeing the prevention of being purged,
                // first of all.
                // For details, see the comment in AccountIndex::do_checked_scan_accounts(),
                // which is referring back here.
                panic!("{message}");
            } else if fallback_to_slow_path {
                // the above bad-index-entry check must had been checked first to retain the same
                // behavior
                return Some((
                    maybe_account_accessor.expect("must be some if clone_in_lock=true"),
                    new_slot,
                ));
            }

            slot = new_slot;
            storage_location = new_storage_location;
        }
    }

    fn do_load(
        &self,
        ancestors: &Ancestors,
        pubkey: &Pubkey,
        max_root: Option<Slot>,
        load_hint: LoadHint,
        load_zero_lamports: LoadZeroLamports,
    ) -> Option<(AccountSharedData, Slot)> {
        self.do_load_with_populate_read_cache(
            ancestors,
            pubkey,
            max_root,
            load_hint,
            false,
            load_zero_lamports,
        )
    }

    /// Load account with `pubkey` and maybe put into read cache.
    ///
    /// If the account is not already cached, invoke `should_put_in_read_cache_fn`.
    /// The caller can inspect the account and indicate if it should be put into the read cache or not.
    ///
    /// Return the account and the slot when the account was last stored.
    /// Return None for ZeroLamport accounts.
    pub fn load_account_with(
        &self,
        ancestors: &Ancestors,
        pubkey: &Pubkey,
        should_put_in_read_cache_fn: impl Fn(&AccountSharedData) -> bool,
    ) -> Option<(AccountSharedData, Slot)> {
        let (slot, storage_location, _maybe_account_accesor) =
            self.read_index_for_accessor_or_load_slow(ancestors, pubkey, None, false)?;
        // Notice the subtle `?` at previous line, we bail out pretty early if missing.

        let in_write_cache = storage_location.is_cached();
        if !in_write_cache {
            let result = self.read_only_accounts_cache.load(*pubkey, slot);
            if let Some(account) = result {
                if account.is_zero_lamport() {
                    return None;
                }
                return Some((account, slot));
            }
        }

        let (mut account_accessor, slot) = self.retry_to_get_account_accessor(
            slot,
            storage_location,
            ancestors,
            pubkey,
            None,
            LoadHint::Unspecified,
        )?;

        // note that the account being in the cache could be different now than it was previously
        // since the cache could be flushed in between the 2 calls.
        let in_write_cache = matches!(account_accessor, LoadedAccountAccessor::Cached(_));
        let account = account_accessor.check_and_get_loaded_account_shared_data();
        if account.is_zero_lamport() {
            return None;
        }

        if !in_write_cache && should_put_in_read_cache_fn(&account) {
            /*
            We show this store into the read-only cache for account 'A' and future loads of 'A' from the read-only cache are
            safe/reflect 'A''s latest state on this fork.
            This safety holds if during replay of slot 'S', we show we only read 'A' from the write cache,
            not the read-only cache, after it's been updated in replay of slot 'S'.
            Assume for contradiction this is not true, and we read 'A' from the read-only cache *after* it had been updated in 'S'.
            This means an entry '(S, A)' was added to the read-only cache after 'A' had been updated in 'S'.
            Now when '(S, A)' was being added to the read-only cache, it must have been true that  'is_cache == false',
            which means '(S', A)' does not exist in the write cache yet.
            However, by the assumption for contradiction above ,  'A' has already been updated in 'S' which means '(S, A)'
            must exist in the write cache, which is a contradiction.
            */
            self.read_only_accounts_cache
                .store(*pubkey, slot, account.clone());
        }
        Some((account, slot))
    }

    /// if 'load_into_read_cache_only', then return value is meaningless.
    ///   The goal is to get the account into the read-only cache.
    fn do_load_with_populate_read_cache(
        &self,
        ancestors: &Ancestors,
        pubkey: &Pubkey,
        max_root: Option<Slot>,
        load_hint: LoadHint,
        load_into_read_cache_only: bool,
        load_zero_lamports: LoadZeroLamports,
    ) -> Option<(AccountSharedData, Slot)> {
        #[cfg(not(test))]
        assert!(max_root.is_none());

        let starting_max_root = self.accounts_index.max_root_inclusive();

        let (slot, storage_location, _maybe_account_accesor) =
            self.read_index_for_accessor_or_load_slow(ancestors, pubkey, max_root, false)?;
        // Notice the subtle `?` at previous line, we bail out pretty early if missing.

        let in_write_cache = storage_location.is_cached();
        if !load_into_read_cache_only {
            if !in_write_cache {
                let result = self.read_only_accounts_cache.load(*pubkey, slot);
                if let Some(account) = result {
                    if matches!(load_zero_lamports, LoadZeroLamports::None)
                        && account.is_zero_lamport()
                    {
                        return None;
                    }
                    return Some((account, slot));
                }
            }
        } else {
            // goal is to load into read cache
            if in_write_cache {
                // no reason to load in read cache. already in write cache
                return None;
            }
            if self.read_only_accounts_cache.in_cache(pubkey, slot) {
                // already in read cache
                return None;
            }
        }

        let (mut account_accessor, slot) = self.retry_to_get_account_accessor(
            slot,
            storage_location,
            ancestors,
            pubkey,
            max_root,
            load_hint,
        )?;
        // note that the account being in the cache could be different now than it was previously
        // since the cache could be flushed in between the 2 calls.
        let in_write_cache = matches!(account_accessor, LoadedAccountAccessor::Cached(_));
        let account = account_accessor.check_and_get_loaded_account_shared_data();
        if matches!(load_zero_lamports, LoadZeroLamports::None) && account.is_zero_lamport() {
            return None;
        }

        if !in_write_cache && load_hint != LoadHint::FixedMaxRootDoNotPopulateReadCache {
            /*
            We show this store into the read-only cache for account 'A' and future loads of 'A' from the read-only cache are
            safe/reflect 'A''s latest state on this fork.
            This safety holds if during replay of slot 'S', we show we only read 'A' from the write cache,
            not the read-only cache, after it's been updated in replay of slot 'S'.
            Assume for contradiction this is not true, and we read 'A' from the read-only cache *after* it had been updated in 'S'.
            This means an entry '(S, A)' was added to the read-only cache after 'A' had been updated in 'S'.
            Now when '(S, A)' was being added to the read-only cache, it must have been true that  'is_cache == false',
            which means '(S', A)' does not exist in the write cache yet.
            However, by the assumption for contradiction above ,  'A' has already been updated in 'S' which means '(S, A)'
            must exist in the write cache, which is a contradiction.
            */
            self.read_only_accounts_cache
                .store(*pubkey, slot, account.clone());
        }
        if load_hint == LoadHint::FixedMaxRoot
            || load_hint == LoadHint::FixedMaxRootDoNotPopulateReadCache
        {
            // If the load hint is that the max root is fixed, the max root should be fixed.
            let ending_max_root = self.accounts_index.max_root_inclusive();
            if starting_max_root != ending_max_root {
                warn!(
                    "do_load_with_populate_read_cache() scanning pubkey {pubkey} called with \
                    fixed max root, but max root changed from {starting_max_root} to \
                    {ending_max_root} during function call"
                );
            }
        }
        Some((account, slot))
    }

    pub fn load_account_hash(
        &self,
        ancestors: &Ancestors,
        pubkey: &Pubkey,
        max_root: Option<Slot>,
        load_hint: LoadHint,
    ) -> Option<AccountHash> {
        let (slot, storage_location, _maybe_account_accesor) =
            self.read_index_for_accessor_or_load_slow(ancestors, pubkey, max_root, false)?;
        // Notice the subtle `?` at previous line, we bail out pretty early if missing.

        let (mut account_accessor, _) = self.retry_to_get_account_accessor(
            slot,
            storage_location,
            ancestors,
            pubkey,
            max_root,
            load_hint,
        )?;
        account_accessor
            .check_and_get_loaded_account(|loaded_account| Some(loaded_account.loaded_hash()))
    }

    fn get_account_accessor<'a>(
        &'a self,
        slot: Slot,
        pubkey: &'a Pubkey,
        storage_location: &StorageLocation,
    ) -> LoadedAccountAccessor<'a> {
        match storage_location {
            StorageLocation::Cached => {
                let maybe_cached_account = self.accounts_cache.load(slot, pubkey).map(Cow::Owned);
                LoadedAccountAccessor::Cached(maybe_cached_account)
            }
            StorageLocation::AppendVec(store_id, offset) => {
                let maybe_storage_entry = self
                    .storage
                    .get_account_storage_entry(slot, *store_id)
                    .map(|account_storage_entry| (account_storage_entry, *offset));
                LoadedAccountAccessor::Stored(maybe_storage_entry)
            }
        }
    }

    fn has_space_available(&self, slot: Slot, size: u64) -> bool {
        let store = self.storage.get_slot_storage_entry(slot).unwrap();
        if store.status() == AccountStorageStatus::Available
            && store.accounts.remaining_bytes() >= size
        {
            return true;
        }
        false
    }

    fn create_store(
        &self,
        slot: Slot,
        size: u64,
        from: &str,
        paths: &[PathBuf],
    ) -> Arc<AccountStorageEntry> {
        self.stats
            .create_store_count
            .fetch_add(1, Ordering::Relaxed);
        let path_index = thread_rng().gen_range(0..paths.len());
        let store = Arc::new(self.new_storage_entry(slot, Path::new(&paths[path_index]), size));

        debug!(
            "creating store: {} slot: {} len: {} size: {} from: {} path: {}",
            store.id(),
            slot,
            store.accounts.len(),
            store.accounts.capacity(),
            from,
            store.accounts.path().display(),
        );

        store
    }

    fn create_and_insert_store(
        &self,
        slot: Slot,
        size: u64,
        from: &str,
    ) -> Arc<AccountStorageEntry> {
        self.create_and_insert_store_with_paths(slot, size, from, &self.paths)
    }

    fn create_and_insert_store_with_paths(
        &self,
        slot: Slot,
        size: u64,
        from: &str,
        paths: &[PathBuf],
    ) -> Arc<AccountStorageEntry> {
        let store = self.create_store(slot, size, from, paths);
        let store_for_index = store.clone();

        self.insert_store(slot, store_for_index);
        store
    }

    fn insert_store(&self, slot: Slot, store: Arc<AccountStorageEntry>) {
        self.storage.insert(slot, store)
    }

    pub fn enable_bank_drop_callback(&self) {
        self.is_bank_drop_callback_enabled
            .store(true, Ordering::Release);
    }

    /// This should only be called after the `Bank::drop()` runs in bank.rs, See BANK_DROP_SAFETY
    /// comment below for more explanation.
    /// * `is_serialized_with_abs` - indicates whether this call runs sequentially
    ///   with all other accounts_db relevant calls, such as shrinking, purging etc.,
    ///   in accounts background service.
    pub fn purge_slot(&self, slot: Slot, bank_id: BankId, is_serialized_with_abs: bool) {
        if self.is_bank_drop_callback_enabled.load(Ordering::Acquire) && !is_serialized_with_abs {
            panic!(
                "bad drop callpath detected; Bank::drop() must run serially with other logic in \
                 ABS like clean_accounts()"
            )
        }

        // BANK_DROP_SAFETY: Because this function only runs once the bank is dropped,
        // we know that there are no longer any ongoing scans on this bank, because scans require
        // and hold a reference to the bank at the tip of the fork they're scanning. Hence it's
        // safe to remove this bank_id from the `removed_bank_ids` list at this point.
        if self
            .accounts_index
            .removed_bank_ids
            .lock()
            .unwrap()
            .remove(&bank_id)
        {
            // If this slot was already cleaned up, no need to do any further cleans
            return;
        }

        self.purge_slots(std::iter::once(&slot));
    }

    /// Purges every slot in `removed_slots` from both the cache and storage. This includes
    /// entries in the accounts index, cache entries, and any backing storage entries.
    pub fn purge_slots_from_cache_and_store<'a>(
        &self,
        removed_slots: impl Iterator<Item = &'a Slot> + Clone,
        purge_stats: &PurgeStats,
        log_accounts: bool,
    ) {
        let mut remove_cache_elapsed_across_slots = 0;
        let mut num_cached_slots_removed = 0;
        let mut total_removed_cached_bytes = 0;
        if log_accounts {
            if let Some(min) = removed_slots.clone().min() {
                info!(
                    "purge_slots_from_cache_and_store: {:?}",
                    self.get_pubkey_hash_for_slot(*min).0
                );
            }
        }
        for remove_slot in removed_slots {
            // This function is only currently safe with respect to `flush_slot_cache()` because
            // both functions run serially in AccountsBackgroundService.
            let mut remove_cache_elapsed = Measure::start("remove_cache_elapsed");
            // Note: we cannot remove this slot from the slot cache until we've removed its
            // entries from the accounts index first. This is because `scan_accounts()` relies on
            // holding the index lock, finding the index entry, and then looking up the entry
            // in the cache. If it fails to find that entry, it will panic in `get_loaded_account()`
            if let Some(slot_cache) = self.accounts_cache.slot_cache(*remove_slot) {
                // If the slot is still in the cache, remove the backing storages for
                // the slot and from the Accounts Index
                num_cached_slots_removed += 1;
                total_removed_cached_bytes += slot_cache.total_bytes();
                self.purge_slot_cache(*remove_slot, &slot_cache);
                remove_cache_elapsed.stop();
                remove_cache_elapsed_across_slots += remove_cache_elapsed.as_us();
                // Nobody else should have removed the slot cache entry yet
                assert!(self.accounts_cache.remove_slot(*remove_slot).is_some());
            } else {
                self.purge_slot_storage(*remove_slot, purge_stats);
            }
            // It should not be possible that a slot is neither in the cache or storage. Even in
            // a slot with all ticks, `Bank::new_from_parent()` immediately stores some sysvars
            // on bank creation.
        }

        purge_stats
            .remove_cache_elapsed
            .fetch_add(remove_cache_elapsed_across_slots, Ordering::Relaxed);
        purge_stats
            .num_cached_slots_removed
            .fetch_add(num_cached_slots_removed, Ordering::Relaxed);
        purge_stats
            .total_removed_cached_bytes
            .fetch_add(total_removed_cached_bytes, Ordering::Relaxed);
    }

    /// Purge the backing storage entries for the given slot, does not purge from
    /// the cache!
    fn purge_dead_slots_from_storage<'a>(
        &'a self,
        removed_slots: impl Iterator<Item = &'a Slot> + Clone,
        purge_stats: &PurgeStats,
    ) {
        // Check all slots `removed_slots` are no longer "relevant" roots.
        // Note that the slots here could have been rooted slots, but if they're passed here
        // for removal it means:
        // 1) All updates in that old root have been outdated by updates in newer roots
        // 2) Those slots/roots should have already been purged from the accounts index root
        // tracking metadata via `accounts_index.clean_dead_slot()`.
        let mut safety_checks_elapsed = Measure::start("safety_checks_elapsed");
        assert!(self
            .accounts_index
            .get_rooted_from_list(removed_slots.clone())
            .is_empty());
        safety_checks_elapsed.stop();
        purge_stats
            .safety_checks_elapsed
            .fetch_add(safety_checks_elapsed.as_us(), Ordering::Relaxed);

        let mut total_removed_stored_bytes = 0;
        let mut all_removed_slot_storages = vec![];

        let mut remove_storage_entries_elapsed = Measure::start("remove_storage_entries_elapsed");
        for remove_slot in removed_slots {
            // Remove the storage entries and collect some metrics
            if let Some(store) = self.storage.remove(remove_slot, false) {
                total_removed_stored_bytes += store.accounts.capacity();
                all_removed_slot_storages.push(store);
            }
        }
        remove_storage_entries_elapsed.stop();
        let num_stored_slots_removed = all_removed_slot_storages.len();

        // Backing mmaps for removed storages entries explicitly dropped here outside
        // of any locks
        let mut drop_storage_entries_elapsed = Measure::start("drop_storage_entries_elapsed");
        drop(all_removed_slot_storages);
        drop_storage_entries_elapsed.stop();

        purge_stats
            .remove_storage_entries_elapsed
            .fetch_add(remove_storage_entries_elapsed.as_us(), Ordering::Relaxed);
        purge_stats
            .drop_storage_entries_elapsed
            .fetch_add(drop_storage_entries_elapsed.as_us(), Ordering::Relaxed);
        purge_stats
            .num_stored_slots_removed
            .fetch_add(num_stored_slots_removed, Ordering::Relaxed);
        purge_stats
            .total_removed_storage_entries
            .fetch_add(num_stored_slots_removed, Ordering::Relaxed);
        purge_stats
            .total_removed_stored_bytes
            .fetch_add(total_removed_stored_bytes, Ordering::Relaxed);
        self.stats
            .dropped_stores
            .fetch_add(num_stored_slots_removed as u64, Ordering::Relaxed);
    }

    fn purge_slot_cache(&self, purged_slot: Slot, slot_cache: &SlotCache) {
        let pubkey_to_slot_set: Vec<(Pubkey, Slot)> = slot_cache
            .iter()
            .map(|account| (*account.key(), purged_slot))
            .collect();
        self.purge_slot_cache_pubkeys(purged_slot, pubkey_to_slot_set, true);
    }

    fn purge_slot_cache_pubkeys(
        &self,
        purged_slot: Slot,
        pubkey_to_slot_set: Vec<(Pubkey, Slot)>,
        is_dead: bool,
    ) {
        // Slot purged from cache should not exist in the backing store
        assert!(self
            .storage
            .get_slot_storage_entry_shrinking_in_progress_ok(purged_slot)
            .is_none());
        let num_purged_keys = pubkey_to_slot_set.len();
        let (reclaims, _) = self.purge_keys_exact(pubkey_to_slot_set.iter());
        assert_eq!(reclaims.len(), num_purged_keys);
        if is_dead {
            self.remove_dead_slots_metadata(std::iter::once(&purged_slot));
        }
    }

    fn purge_slot_storage(&self, remove_slot: Slot, purge_stats: &PurgeStats) {
        // Because AccountsBackgroundService synchronously flushes from the accounts cache
        // and handles all Bank::drop() (the cleanup function that leads to this
        // function call), then we don't need to worry above an overlapping cache flush
        // with this function call. This means, if we get into this case, we can be
        // confident that the entire state for this slot has been flushed to the storage
        // already.
        let mut scan_storages_elapsed = Measure::start("scan_storages_elapsed");
        let mut stored_keys = HashSet::new();
        if let Some(storage) = self
            .storage
            .get_slot_storage_entry_shrinking_in_progress_ok(remove_slot)
        {
            storage
                .accounts
                .scan_pubkeys(|pk| {
                    stored_keys.insert((*pk, remove_slot));
                })
                .expect("must scan accounts storage");
        }
        scan_storages_elapsed.stop();
        purge_stats
            .scan_storages_elapsed
            .fetch_add(scan_storages_elapsed.as_us(), Ordering::Relaxed);

        let mut purge_accounts_index_elapsed = Measure::start("purge_accounts_index_elapsed");
        // Purge this slot from the accounts index
        let (reclaims, pubkeys_removed_from_accounts_index) =
            self.purge_keys_exact(stored_keys.iter());
        purge_accounts_index_elapsed.stop();
        purge_stats
            .purge_accounts_index_elapsed
            .fetch_add(purge_accounts_index_elapsed.as_us(), Ordering::Relaxed);

        // `handle_reclaims()` should remove all the account index entries and
        // storage entries
        let mut handle_reclaims_elapsed = Measure::start("handle_reclaims_elapsed");
        // Slot should be dead after removing all its account entries
        // There is no reason to mark accounts obsolete as the slot storage is being purged
        let expected_dead_slot = Some(remove_slot);
        self.handle_reclaims(
            (!reclaims.is_empty()).then(|| reclaims.iter()),
            expected_dead_slot,
            &pubkeys_removed_from_accounts_index,
            HandleReclaims::ProcessDeadSlots(purge_stats),
            MarkAccountsObsolete::No,
        );
        handle_reclaims_elapsed.stop();
        purge_stats
            .handle_reclaims_elapsed
            .fetch_add(handle_reclaims_elapsed.as_us(), Ordering::Relaxed);
        // After handling the reclaimed entries, this slot's
        // storage entries should be purged from self.storage
        assert!(
            self.storage.get_slot_storage_entry(remove_slot).is_none(),
            "slot {remove_slot} is not none"
        );
    }

    fn purge_slots<'a>(&self, slots: impl Iterator<Item = &'a Slot> + Clone) {
        // `add_root()` should be called first
        let mut safety_checks_elapsed = Measure::start("safety_checks_elapsed");
        let non_roots = slots
            // Only safe to check when there are duplicate versions of a slot
            // because ReplayStage will not make new roots before dumping the
            // duplicate slots first. Thus we will not be in a case where we
            // root slot `S`, then try to dump some other version of slot `S`, the
            // dumping has to finish first
            //
            // Also note roots are never removed via `remove_unrooted_slot()`, so
            // it's safe to filter them out here as they won't need deletion from
            // self.accounts_index.removed_bank_ids in `purge_slots_from_cache_and_store()`.
            .filter(|slot| !self.accounts_index.is_alive_root(**slot));
        safety_checks_elapsed.stop();
        self.external_purge_slots_stats
            .safety_checks_elapsed
            .fetch_add(safety_checks_elapsed.as_us(), Ordering::Relaxed);
        self.purge_slots_from_cache_and_store(non_roots, &self.external_purge_slots_stats, false);
        self.external_purge_slots_stats
            .report("external_purge_slots_stats", Some(1000));
    }

    pub fn remove_unrooted_slots(&self, remove_slots: &[(Slot, BankId)]) {
        let rooted_slots = self
            .accounts_index
            .get_rooted_from_list(remove_slots.iter().map(|(slot, _)| slot));
        assert!(
            rooted_slots.is_empty(),
            "Trying to remove accounts for rooted slots {rooted_slots:?}"
        );

        let RemoveUnrootedSlotsSynchronization {
            slots_under_contention,
            signal,
        } = &self.remove_unrooted_slots_synchronization;

        {
            // Slots that are currently being flushed by flush_slot_cache()

            let mut currently_contended_slots = slots_under_contention.lock().unwrap();

            // Slots that are currently being flushed by flush_slot_cache() AND
            // we want to remove in this function
            let mut remaining_contended_flush_slots: Vec<Slot> = remove_slots
                .iter()
                .filter_map(|(remove_slot, _)| {
                    // Reserve the slots that we want to purge that aren't currently
                    // being flushed to prevent cache from flushing those slots in
                    // the future.
                    //
                    // Note that the single replay thread has to remove a specific slot `N`
                    // before another version of the same slot can be replayed. This means
                    // multiple threads should not call `remove_unrooted_slots()` simultaneously
                    // with the same slot.
                    let is_being_flushed = !currently_contended_slots.insert(*remove_slot);
                    // If the cache is currently flushing this slot, add it to the list
                    is_being_flushed.then_some(remove_slot)
                })
                .cloned()
                .collect();

            // Wait for cache flushes to finish
            loop {
                if !remaining_contended_flush_slots.is_empty() {
                    // Wait for the signal that the cache has finished flushing a slot
                    //
                    // Don't wait if the remaining_contended_flush_slots is empty, otherwise
                    // we may never get a signal since there's no cache flush thread to
                    // do the signaling
                    currently_contended_slots = signal.wait(currently_contended_slots).unwrap();
                } else {
                    // There are no slots being flushed to wait on, so it's safe to continue
                    // to purging the slots we want to purge!
                    break;
                }

                // For each slot the cache flush has finished, mark that we're about to start
                // purging these slots by reserving it in `currently_contended_slots`.
                remaining_contended_flush_slots.retain(|flush_slot| {
                    // returns true if slot was already in set. This means slot is being flushed
                    !currently_contended_slots.insert(*flush_slot)
                });
            }
        }

        // Mark down these slots are about to be purged so that new attempts to scan these
        // banks fail, and any ongoing scans over these slots will detect that they should abort
        // their results
        {
            let mut locked_removed_bank_ids = self.accounts_index.removed_bank_ids.lock().unwrap();
            for (_slot, remove_bank_id) in remove_slots.iter() {
                locked_removed_bank_ids.insert(*remove_bank_id);
            }
        }

        let remove_unrooted_purge_stats = PurgeStats::default();
        self.purge_slots_from_cache_and_store(
            remove_slots.iter().map(|(slot, _)| slot),
            &remove_unrooted_purge_stats,
            true,
        );
        remove_unrooted_purge_stats.report("remove_unrooted_slots_purge_slots_stats", None);

        let mut currently_contended_slots = slots_under_contention.lock().unwrap();
        for (remove_slot, _) in remove_slots {
            assert!(currently_contended_slots.remove(remove_slot));
        }
    }

    /// Calculates the `AccountLtHash` of `account`
    pub fn lt_hash_account(account: &impl ReadableAccount, pubkey: &Pubkey) -> AccountLtHash {
        if account.lamports() == 0 {
            return ZERO_LAMPORT_ACCOUNT_LT_HASH;
        }

        let hasher = Self::hash_account_helper(account, pubkey, RentEpochInAccountHash::Excluded);
        let lt_hash = LtHash::with(&hasher);
        AccountLtHash(lt_hash)
    }

    /// Calculates the `AccountHash` of `account`
    pub fn hash_account<T: ReadableAccount>(account: &T, pubkey: &Pubkey) -> AccountHash {
        if account.lamports() == 0 {
            return ZERO_LAMPORT_ACCOUNT_HASH;
        }

        let hasher = Self::hash_account_helper(account, pubkey, RentEpochInAccountHash::Included);
        let hash = Hash::new_from_array(hasher.finalize().into());
        AccountHash(hash)
    }

    /// Hashes `account` and returns the underlying Hasher
    fn hash_account_helper(
        account: &impl ReadableAccount,
        pubkey: &Pubkey,
        rent_epoch_in_account_hash: RentEpochInAccountHash,
    ) -> blake3::Hasher {
        let mut hasher = blake3::Hasher::new();

        // allocate a buffer on the stack that's big enough
        // to hold a token account or a stake account
        const META_SIZE: usize = 8 /* lamports */ + 8 /* rent_epoch */ + 1 /* executable */ + 32 /* owner */ + 32 /* pubkey */;
        const DATA_SIZE: usize = 200; // stake accounts are 200 B and token accounts are 165-182ish B
        const BUFFER_SIZE: usize = META_SIZE + DATA_SIZE;
        let mut buffer = SmallVec::<[u8; BUFFER_SIZE]>::new();

        // collect lamports, rent_epoch into buffer to hash
        buffer.extend_from_slice(&account.lamports().to_le_bytes());

        if rent_epoch_in_account_hash == RentEpochInAccountHash::Included {
            // conditionally hash in the rent epoch
            // once the rent epoch is permanently excluded, also remove the 8 bytes in the META_SIZE above
            buffer.extend_from_slice(&account.rent_epoch().to_le_bytes());
        }

        let data = account.data();
        if data.len() > DATA_SIZE {
            // For larger accounts whose data can't fit into the buffer, update the hash now.
            hasher.update(&buffer);
            buffer.clear();

            // hash account's data
            hasher.update(data);
        } else {
            // For small accounts whose data can fit into the buffer, append it to the buffer.
            buffer.extend_from_slice(data);
        }

        // collect exec_flag, owner, pubkey into buffer to hash
        buffer.push(account.executable().into());
        buffer.extend_from_slice(account.owner().as_ref());
        buffer.extend_from_slice(pubkey.as_ref());
        hasher.update(&buffer);

        hasher
    }

    fn write_accounts_to_storage<'a>(
        &self,
        slot: Slot,
        storage: &AccountStorageEntry,
        accounts_and_meta_to_store: &impl StorableAccounts<'a>,
    ) -> Vec<AccountInfo> {
        let mut infos: Vec<AccountInfo> = Vec::with_capacity(accounts_and_meta_to_store.len());
        let mut total_append_accounts_us = 0;
        while infos.len() < accounts_and_meta_to_store.len() {
            let mut append_accounts = Measure::start("append_accounts");
            let stored_accounts_info = storage
                .accounts
                .write_accounts(accounts_and_meta_to_store, infos.len());
            append_accounts.stop();
            total_append_accounts_us += append_accounts.as_us();
            let Some(stored_accounts_info) = stored_accounts_info else {
                storage.set_status(AccountStorageStatus::Full);

                // See if an account overflows the append vecs in the slot.
                let data_len = accounts_and_meta_to_store.data_len(infos.len());
                let data_len = (data_len + STORE_META_OVERHEAD) as u64;
                if !self.has_space_available(slot, data_len) {
                    info!(
                        "write_accounts_to_storage, no space: {}, {}, {}, {}, {}",
                        storage.accounts.capacity(),
                        storage.accounts.remaining_bytes(),
                        data_len,
                        infos.len(),
                        accounts_and_meta_to_store.len()
                    );
                    let special_store_size = std::cmp::max(data_len * 2, self.file_size);
                    self.create_and_insert_store(slot, special_store_size, "large create");
                }
                continue;
            };

            let store_id = storage.id();
            for (i, offset) in stored_accounts_info.offsets.iter().enumerate() {
                infos.push(AccountInfo::new(
                    StorageLocation::AppendVec(store_id, *offset),
                    accounts_and_meta_to_store.is_zero_lamport(i),
                ));
            }
            storage.add_accounts(
                stored_accounts_info.offsets.len(),
                stored_accounts_info.size,
            );

            // restore the state to available
            storage.set_status(AccountStorageStatus::Available);
        }

        self.stats
            .store_append_accounts
            .fetch_add(total_append_accounts_us, Ordering::Relaxed);

        infos
    }

    pub fn mark_slot_frozen(&self, slot: Slot) {
        if let Some(slot_cache) = self.accounts_cache.slot_cache(slot) {
            slot_cache.mark_slot_frozen();
            slot_cache.report_slot_store_metrics();
        }
        self.accounts_cache.report_size();
    }

    // These functions/fields are only usable from a dev context (i.e. tests and benches)
    #[cfg(feature = "dev-context-only-utils")]
    pub fn flush_accounts_cache_slot_for_tests(&self, slot: Slot) {
        self.flush_slot_cache(slot);
    }

    /// true if write cache is too big
    fn should_aggressively_flush_cache(&self) -> bool {
        self.write_cache_limit_bytes
            .unwrap_or(WRITE_CACHE_LIMIT_BYTES_DEFAULT)
            < self.accounts_cache.size()
    }

    // `force_flush` flushes all the cached roots `<= requested_flush_root`. It also then
    // flushes:
    // 1) excess remaining roots or unrooted slots while 'should_aggressively_flush_cache' is true
    pub fn flush_accounts_cache(&self, force_flush: bool, requested_flush_root: Option<Slot>) {
        #[cfg(not(test))]
        assert!(requested_flush_root.is_some());

        if !force_flush && !self.should_aggressively_flush_cache() {
            return;
        }

        // Flush only the roots <= requested_flush_root, so that snapshotting has all
        // the relevant roots in storage.
        let mut flush_roots_elapsed = Measure::start("flush_roots_elapsed");

        let _guard = self.active_stats.activate(ActiveStatItem::Flush);

        // Note even if force_flush is false, we will still flush all roots <= the
        // given `requested_flush_root`, even if some of the later roots cannot be used for
        // cleaning due to an ongoing scan
        let (total_new_cleaned_roots, num_cleaned_roots_flushed, mut flush_stats) = self
            .flush_rooted_accounts_cache(
                requested_flush_root,
                true, // should_clean
            );
        flush_roots_elapsed.stop();

        // Note we don't purge unrooted slots here because there may be ongoing scans/references
        // for those slot, let the Bank::drop() implementation do cleanup instead on dead
        // banks

        // If 'should_aggressively_flush_cache', then flush the excess ones to storage
        let (total_new_excess_roots, num_excess_roots_flushed, flush_stats_aggressively) =
            if self.should_aggressively_flush_cache() {
                // Start by flushing the roots
                //
                // Cannot do any cleaning on roots past `requested_flush_root` because future
                // snapshots may need updates from those later slots, hence we pass `false`
                // for `should_clean`.
                self.flush_rooted_accounts_cache(None, false)
            } else {
                (0, 0, FlushStats::default())
            };
        flush_stats.accumulate(&flush_stats_aggressively);

        let mut excess_slot_count = 0;
        let mut unflushable_unrooted_slot_count = 0;
        let max_flushed_root = self.accounts_cache.fetch_max_flush_root();
        if self.should_aggressively_flush_cache() {
            let mut old_slots = self.accounts_cache.cached_frozen_slots();
            old_slots.sort_unstable();
            excess_slot_count = old_slots.len();
            let mut flush_stats = FlushStats::default();
            old_slots.into_iter().for_each(|old_slot| {
                // Don't flush slots that are known to be unrooted
                if old_slot > max_flushed_root {
                    if self.should_aggressively_flush_cache() {
                        if let Some(stats) = self.flush_slot_cache(old_slot) {
                            flush_stats.accumulate(&stats);
                        }
                    }
                } else {
                    unflushable_unrooted_slot_count += 1;
                }
            });
            datapoint_info!(
                "accounts_db-flush_accounts_cache_aggressively",
                (
                    "num_accounts_flushed",
                    flush_stats.num_accounts_flushed.0,
                    i64
                ),
                ("num_accounts_saved", flush_stats.num_accounts_purged.0, i64),
                (
                    "account_bytes_flushed",
                    flush_stats.num_bytes_flushed.0,
                    i64
                ),
                ("account_bytes_saved", flush_stats.num_bytes_purged.0, i64),
                ("total_cache_size", self.accounts_cache.size(), i64),
                ("total_frozen_slots", excess_slot_count, i64),
                ("total_slots", self.accounts_cache.num_slots(), i64),
            );
        }

        datapoint_info!(
            "accounts_db-flush_accounts_cache",
            ("total_new_cleaned_roots", total_new_cleaned_roots, i64),
            ("num_cleaned_roots_flushed", num_cleaned_roots_flushed, i64),
            ("total_new_excess_roots", total_new_excess_roots, i64),
            ("num_excess_roots_flushed", num_excess_roots_flushed, i64),
            ("excess_slot_count", excess_slot_count, i64),
            (
                "unflushable_unrooted_slot_count",
                unflushable_unrooted_slot_count,
                i64
            ),
            ("flush_roots_elapsed", flush_roots_elapsed.as_us(), i64),
            (
                "account_bytes_flushed",
                flush_stats.num_bytes_flushed.0,
                i64
            ),
            (
                "num_accounts_flushed",
                flush_stats.num_accounts_flushed.0,
                i64
            ),
            ("account_bytes_saved", flush_stats.num_bytes_purged.0, i64),
            ("num_accounts_saved", flush_stats.num_accounts_purged.0, i64),
            (
                "store_accounts_total_us",
                flush_stats.store_accounts_total_us.0,
                i64
            ),
            (
                "update_index_us",
                flush_stats.store_accounts_timing.update_index_elapsed,
                i64
            ),
            (
                "store_accounts_elapsed_us",
                flush_stats.store_accounts_timing.store_accounts_elapsed,
                i64
            ),
            (
                "handle_reclaims_elapsed_us",
                flush_stats.store_accounts_timing.handle_reclaims_elapsed,
                i64
            ),
        );
    }

    fn flush_rooted_accounts_cache(
        &self,
        requested_flush_root: Option<Slot>,
        should_clean: bool,
    ) -> (usize, usize, FlushStats) {
        let max_clean_root = should_clean
            .then(|| {
                // If there is a long running scan going on, this could prevent any cleaning
                // based on updates from slots > `max_clean_root`.
                self.max_clean_root(requested_flush_root)
            })
            .flatten();

        let mut written_accounts = HashSet::new();

        // If `should_clean` is false, then`should_flush_f` will be None, which will cause
        // `flush_slot_cache` to flush all accounts to storage without cleaning any accounts.
        let mut should_flush_f = should_clean
            .then(|| {
                Some(move |&pubkey: &Pubkey| {
                    // if not in hashset, then not flushed previously, so flush it
                    written_accounts.insert(pubkey)
                })
            })
            .flatten();

        // Always flush up to `requested_flush_root`, which is necessary for things like snapshotting.
        let flushed_roots: BTreeSet<Slot> = self.accounts_cache.clear_roots(requested_flush_root);

        // Iterate from highest to lowest so that we don't need to flush earlier
        // outdated updates in earlier roots
        let mut num_roots_flushed = 0;
        let mut flush_stats = FlushStats::default();
        for &root in flushed_roots.iter().rev() {
            if let Some(stats) =
                self.flush_slot_cache_with_clean(root, should_flush_f.as_mut(), max_clean_root)
            {
                num_roots_flushed += 1;
                flush_stats.accumulate(&stats);
            }
        }

        // Note that self.flush_slot_cache_with_clean() can return None if the
        // slot is already been flushed. This can happen if the cache is
        // overwhelmed and we flushed some yet to be rooted frozen slots.
        // However, independent of whether the last slot was actually flushed
        // from the cache by the above loop, we should always update the
        // `max_flush_root` to the max of the flushed roots, because that's
        // max_flushed_root tracks the logical last root that was flushed to
        // storage by snapshotting.
        if let Some(&root) = flushed_roots.last() {
            self.accounts_cache.set_max_flush_root(root);
        }
        let num_new_roots = flushed_roots.len();
        (num_new_roots, num_roots_flushed, flush_stats)
    }

    fn do_flush_slot_cache(
        &self,
        slot: Slot,
        slot_cache: &SlotCache,
        mut should_flush_f: Option<&mut impl FnMut(&Pubkey) -> bool>,
        max_clean_root: Option<Slot>,
    ) -> FlushStats {
        let mut flush_stats = FlushStats::default();
        let iter_items: Vec<_> = slot_cache.iter().collect();
        let mut pubkey_to_slot_set: Vec<(Pubkey, Slot)> = vec![];
        if should_flush_f.is_some() {
            if let Some(max_clean_root) = max_clean_root {
                if slot > max_clean_root {
                    // Only if the root is greater than the `max_clean_root` do we
                    // have to prevent cleaning, otherwise, just default to `should_flush_f`
                    // for any slots <= `max_clean_root`
                    should_flush_f = None;
                }
            }
        }

        let accounts: Vec<(&Pubkey, &AccountSharedData)> = iter_items
            .iter()
            .filter_map(|iter_item| {
                let key = iter_item.key();
                let account = &iter_item.value().account;
                let should_flush = should_flush_f
                    .as_mut()
                    .map(|should_flush_f| should_flush_f(key))
                    .unwrap_or(true);
                if should_flush {
                    flush_stats.num_bytes_flushed +=
                        aligned_stored_size(account.data().len()) as u64;
                    flush_stats.num_accounts_flushed += 1;
                    Some((key, account))
                } else {
                    // If we don't flush, we have to remove the entry from the
                    // index, since it's equivalent to purging
                    pubkey_to_slot_set.push((*key, slot));
                    flush_stats.num_bytes_purged +=
                        aligned_stored_size(account.data().len()) as u64;
                    flush_stats.num_accounts_purged += 1;
                    None
                }
            })
            .collect();

        let is_dead_slot = accounts.is_empty();
        // Remove the account index entries from earlier roots that are outdated by later roots.
        // Safe because queries to the index will be reading updates from later roots.
        self.purge_slot_cache_pubkeys(slot, pubkey_to_slot_set, is_dead_slot);

        if !is_dead_slot {
            // This ensures that all updates are written to an AppendVec, before any
            // updates to the index happen, so anybody that sees a real entry in the index,
            // will be able to find the account in storage
            let flushed_store = self.create_and_insert_store(
                slot,
                flush_stats.num_bytes_flushed.0,
                "flush_slot_cache",
            );
            let (store_accounts_timing_inner, store_accounts_total_inner_us) =
                measure_us!(self.store_accounts_frozen((slot, &accounts[..]), &flushed_store,));
            flush_stats.store_accounts_timing = store_accounts_timing_inner;
            flush_stats.store_accounts_total_us = Saturating(store_accounts_total_inner_us);

            // If the above sizing function is correct, just one AppendVec is enough to hold
            // all the data for the slot
            assert!(self.storage.get_slot_storage_entry(slot).is_some());
            self.reopen_storage_as_readonly_shrinking_in_progress_ok(slot);
        }

        // Remove this slot from the cache, which will to AccountsDb's new readers should look like an
        // atomic switch from the cache to storage.
        // There is some racy condition for existing readers who just has read exactly while
        // flushing. That case is handled by retry_to_get_account_accessor()
        assert!(self.accounts_cache.remove_slot(slot).is_some());

        // Add `accounts` to uncleaned_pubkeys since we know they were written
        // to a storage and should be visited by `clean`.
        self.uncleaned_pubkeys
            .entry(slot)
            .or_default()
            .extend(accounts.iter().map(|(pubkey, _account)| **pubkey));

        flush_stats
    }

    /// flush all accounts in this slot
    fn flush_slot_cache(&self, slot: Slot) -> Option<FlushStats> {
        self.flush_slot_cache_with_clean(slot, None::<&mut fn(&_) -> bool>, None)
    }

    /// `should_flush_f` is an optional closure that determines whether a given
    /// account should be flushed. Passing `None` will by default flush all
    /// accounts
    fn flush_slot_cache_with_clean(
        &self,
        slot: Slot,
        should_flush_f: Option<&mut impl FnMut(&Pubkey) -> bool>,
        max_clean_root: Option<Slot>,
    ) -> Option<FlushStats> {
        if self
            .remove_unrooted_slots_synchronization
            .slots_under_contention
            .lock()
            .unwrap()
            .insert(slot)
        {
            // We have not seen this slot, flush it.
            let flush_stats = self.accounts_cache.slot_cache(slot).map(|slot_cache| {
                #[cfg(test)]
                {
                    // Give some time for cache flushing to occur here for unit tests
                    sleep(Duration::from_millis(self.load_delay));
                }
                // Since we added the slot to `slots_under_contention` AND this slot
                // still exists in the cache, we know the slot cannot be removed
                // by any other threads past this point. We are now responsible for
                // flushing this slot.
                self.do_flush_slot_cache(slot, &slot_cache, should_flush_f, max_clean_root)
            });

            // Nobody else should have been purging this slot, so should not have been removed
            // from `self.remove_unrooted_slots_synchronization`.
            assert!(self
                .remove_unrooted_slots_synchronization
                .slots_under_contention
                .lock()
                .unwrap()
                .remove(&slot));

            // Signal to any threads blocked on `remove_unrooted_slots(slot)` that we have finished
            // flushing
            self.remove_unrooted_slots_synchronization
                .signal
                .notify_all();
            flush_stats
        } else {
            // We have already seen this slot. It is already under flushing. Skip.
            None
        }
    }

    fn write_accounts_to_cache<'a, 'b>(
        &self,
        slot: Slot,
        accounts_and_meta_to_store: &impl StorableAccounts<'b>,
        txs: Option<&[&SanitizedTransaction]>,
    ) -> Vec<AccountInfo> {
        let mut current_write_version = if self.accounts_update_notifier.is_some() {
            self.write_version
                .fetch_add(accounts_and_meta_to_store.len() as u64, Ordering::AcqRel)
        } else {
            0
        };

        let (account_infos, cached_accounts) = (0..accounts_and_meta_to_store.len())
            .map(|index| {
                let txn = txs.map(|txs| *txs.get(index).expect("txs must be present if provided"));
                let mut account_info = AccountInfo::default();
                accounts_and_meta_to_store.account_default_if_zero_lamport(index, |account| {
                    let account_shared_data = account.to_account_shared_data();
                    let pubkey = account.pubkey();
                    account_info =
                        AccountInfo::new(StorageLocation::Cached, account.is_zero_lamport());

                    self.notify_account_at_accounts_update(
                        slot,
                        &account_shared_data,
                        &txn,
                        pubkey,
                        current_write_version,
                    );
                    current_write_version = current_write_version.saturating_add(1);

                    let cached_account =
                        self.accounts_cache.store(slot, pubkey, account_shared_data);
                    (account_info, cached_account)
                })
            })
            .unzip();

        // hash this accounts in bg
        if let Some(sender) = self.sender_bg_hasher.read().unwrap().as_ref() {
            let _ = sender.send(cached_accounts);
        };

        account_infos
    }

    fn report_store_stats(&self) {
        let mut total_count = 0;
        let mut newest_slot = 0;
        let mut oldest_slot = u64::MAX;
        let mut total_bytes = 0;
        let mut total_alive_bytes = 0;
        for (slot, store) in self.storage.iter() {
            total_count += 1;
            newest_slot = std::cmp::max(newest_slot, slot);

            oldest_slot = std::cmp::min(oldest_slot, slot);

            total_alive_bytes += store.alive_bytes();
            total_bytes += store.capacity();
        }
        info!(
            "total_stores: {total_count}, newest_slot: {newest_slot}, oldest_slot: {oldest_slot}"
        );

        let total_alive_ratio = if total_bytes > 0 {
            total_alive_bytes as f64 / total_bytes as f64
        } else {
            0.
        };

        datapoint_info!(
            "accounts_db-stores",
            ("total_count", total_count, i64),
            ("total_bytes", total_bytes, i64),
            ("total_alive_bytes", total_alive_bytes, i64),
            ("total_alive_ratio", total_alive_ratio, f64),
        );
        datapoint_info!(
            "accounts_db-perf-stats",
            (
                "delta_hash_num",
                self.stats.delta_hash_num.swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "delta_hash_scan_us",
                self.stats
                    .delta_hash_scan_time_total_us
                    .swap(0, Ordering::Relaxed),
                i64
            ),
            (
                "delta_hash_accumulate_us",
                self.stats
                    .delta_hash_accumulate_time_total_us
                    .swap(0, Ordering::Relaxed),
                i64
            ),
        );
    }

    pub fn checked_sum_for_capitalization<T: Iterator<Item = u64>>(balances: T) -> u64 {
        AccountsHasher::checked_cast_for_capitalization(balances.map(|b| b as u128).sum::<u128>())
    }

    pub fn calculate_accounts_hash_from_index(
        &self,
        max_slot: Slot,
        config: &CalcAccountsHashConfig<'_>,
    ) -> (AccountsHash, u64) {
        let mut collect = Measure::start("collect");
        let keys: Vec<_> = self
            .accounts_index
            .account_maps
            .iter()
            .flat_map(|map| {
                let mut keys = map.keys();
                keys.sort_unstable(); // hashmap is not ordered, but bins are relative to each other
                keys
            })
            .collect();
        collect.stop();

        // Pick a chunk size big enough to allow us to produce output vectors that are smaller than the overall size.
        // We'll also accumulate the lamports within each chunk and fewer chunks results in less contention to accumulate the sum.
        let chunks = crate::accounts_hash::MERKLE_FANOUT.pow(4);
        let total_lamports = Mutex::<u64>::new(0);

        let get_account_hashes = || {
            keys.par_chunks(chunks)
                .map(|pubkeys| {
                    let mut sum = 0u128;
                    let account_hashes: Vec<Hash> = pubkeys
                        .iter()
                        .filter_map(|pubkey| {
                            let index_entry = self.accounts_index.get_cloned(pubkey)?;
                            self.accounts_index
                                .get_account_info_with_and_then(
                                    &index_entry,
                                    config.ancestors,
                                    Some(max_slot),
                                    |(slot, account_info)| {
                                        if account_info.is_zero_lamport() {
                                            return None;
                                        }
                                        self.get_account_accessor(
                                            slot,
                                            pubkey,
                                            &account_info.storage_location(),
                                        )
                                        .get_loaded_account(|loaded_account| {
                                            let mut loaded_hash = loaded_account.loaded_hash();
                                            let balance = loaded_account.lamports();
                                            let hash_is_missing =
                                                loaded_hash == AccountHash(Hash::default());
                                            if hash_is_missing {
                                                let computed_hash = Self::hash_account(
                                                    &loaded_account,
                                                    loaded_account.pubkey(),
                                                );
                                                loaded_hash = computed_hash;
                                            }
                                            sum += balance as u128;
                                            loaded_hash.0
                                        })
                                    },
                                )
                                .flatten()
                        })
                        .collect();
                    let mut total = total_lamports.lock().unwrap();
                    *total = AccountsHasher::checked_cast_for_capitalization(*total as u128 + sum);
                    account_hashes
                })
                .collect()
        };

        let mut scan = Measure::start("scan");
        let account_hashes: Vec<Vec<Hash>> = self.thread_pool_clean.install(get_account_hashes);
        scan.stop();

        let total_lamports = *total_lamports.lock().unwrap();

        let mut hash_time = Measure::start("hash");
        let (accumulated_hash, hash_total) = AccountsHasher::calculate_hash(account_hashes);
        hash_time.stop();

        datapoint_info!(
            "calculate_accounts_hash_from_index",
            ("accounts_scan", scan.as_us(), i64),
            ("hash", hash_time.as_us(), i64),
            ("hash_total", hash_total, i64),
            ("collect", collect.as_us(), i64),
        );

        let accounts_hash = AccountsHash(accumulated_hash);
        (accounts_hash, total_lamports)
    }

    /// Calculates the accounts lt hash
    ///
    /// Only intended to be called at startup (or by tests).
    /// Only intended to be used while testing the experimental accumulator hash.
    pub fn calculate_accounts_lt_hash_at_startup_from_index(
        &self,
        ancestors: &Ancestors,
        startup_slot: Slot,
    ) -> AccountsLtHash {
        // This impl iterates over all the index bins in parallel, and computes the lt hash
        // sequentially per bin.  Then afterwards reduces to a single lt hash.
        // This implementation is quite fast.  Runtime is about 150 seconds on mnb as of 10/2/2024.
        // The sequential implementation took about 6,275 seconds!
        // A different parallel implementation that iterated over the bins *sequentially* and then
        // hashed the accounts *within* a bin in parallel took about 600 seconds.  That impl uses
        // less memory, as only a single index bin is loaded into mem at a time.
        let lt_hash = self
            .accounts_index
            .account_maps
            .par_iter()
            .fold(
                LtHash::identity,
                |mut accumulator_lt_hash, accounts_index_bin| {
                    for pubkey in accounts_index_bin.keys() {
                        let account_lt_hash = self
                            .accounts_index
                            .get_with_and_then(
                                &pubkey,
                                Some(ancestors),
                                Some(startup_slot),
                                false,
                                |(slot, account_info)| {
                                    (!account_info.is_zero_lamport()).then(|| {
                                        self.get_account_accessor(
                                            slot,
                                            &pubkey,
                                            &account_info.storage_location(),
                                        )
                                        .get_loaded_account(|loaded_account| {
                                            Self::lt_hash_account(&loaded_account, &pubkey)
                                        })
                                        // SAFETY: The index said this pubkey exists, so
                                        // there must be an account to load.
                                        .unwrap()
                                    })
                                },
                            )
                            .flatten();
                        if let Some(account_lt_hash) = account_lt_hash {
                            accumulator_lt_hash.mix_in(&account_lt_hash.0);
                        }
                    }
                    accumulator_lt_hash
                },
            )
            .reduce(LtHash::identity, |mut accum, elem| {
                accum.mix_in(&elem);
                accum
            });

        AccountsLtHash(lt_hash)
    }

    /// Calculates the accounts lt hash
    ///
    /// Intended to be used to verify the accounts lt hash at startup.
    ///
    /// The `duplicates_lt_hash` is the old/duplicate accounts to mix *out* of the storages.
    /// This value comes from index generation.
    pub fn calculate_accounts_lt_hash_at_startup_from_storages(
        &self,
        storages: &[Arc<AccountStorageEntry>],
        duplicates_lt_hash: &DuplicatesLtHash,
    ) -> AccountsLtHash {
        let mut lt_hash = storages
            .par_iter()
            .fold(LtHash::identity, |mut accum, storage| {
                storage
                    .accounts
                    .scan_accounts(|_offset, account| {
                        let account_lt_hash = Self::lt_hash_account(&account, account.pubkey());
                        accum.mix_in(&account_lt_hash.0);
                    })
                    .expect("must scan accounts storage");
                accum
            })
            .reduce(LtHash::identity, |mut accum, elem| {
                accum.mix_in(&elem);
                accum
            });

        lt_hash.mix_out(&duplicates_lt_hash.0);

        AccountsLtHash(lt_hash)
    }

    /// Calculates the capitalization
    ///
    /// Panics if capitalization overflows a u64.
    ///
    /// Note, this is *very* expensive!  It walks the whole accounts index,
    /// account-by-account, summing each account's balance.
    ///
    /// Only intended to be called at startup by ledger-tool or tests.
    pub fn calculate_capitalization_at_startup_from_index(
        &self,
        ancestors: &Ancestors,
        startup_slot: Slot,
    ) -> u64 {
        self.accounts_index
            .account_maps
            .par_iter()
            .map(|accounts_index_bin| {
                accounts_index_bin
                    .keys()
                    .into_iter()
                    .map(|pubkey| {
                        self.accounts_index
                            .get_with_and_then(
                                &pubkey,
                                Some(ancestors),
                                Some(startup_slot),
                                false,
                                |(slot, account_info)| {
                                    (!account_info.is_zero_lamport()).then(|| {
                                        self.get_account_accessor(
                                            slot,
                                            &pubkey,
                                            &account_info.storage_location(),
                                        )
                                        .get_loaded_account(|loaded_account| {
                                            loaded_account.lamports()
                                        })
                                        // SAFETY: The index said this pubkey exists, so
                                        // there must be an account to load.
                                        .unwrap()
                                    })
                                },
                            )
                            .flatten()
                            .unwrap_or(0)
                    })
                    .try_fold(0, u64::checked_add)
            })
            .try_reduce(|| 0, u64::checked_add)
            .expect("capitalization cannot overflow")
    }

    /// This is only valid to call from tests.
    /// run the accounts hash calculation and store the results
    pub fn update_accounts_hash_for_tests(
        &self,
        slot: Slot,
        ancestors: &Ancestors,
        debug_verify: bool,
        is_startup: bool,
    ) -> (AccountsHash, u64) {
        self.update_accounts_hash_with_verify_from(
            CalcAccountsHashDataSource::IndexForTests,
            debug_verify,
            slot,
            ancestors,
            None,
            &EpochSchedule::default(),
            is_startup,
        )
    }

    fn update_old_slot_stats(&self, stats: &HashStats, storage: Option<&Arc<AccountStorageEntry>>) {
        if let Some(storage) = storage {
            stats.roots_older_than_epoch.fetch_add(1, Ordering::Relaxed);
            let num_accounts = storage.count();
            let sizes = storage.capacity();
            stats
                .append_vec_sizes_older_than_epoch
                .fetch_add(sizes as usize, Ordering::Relaxed);
            stats
                .accounts_in_roots_older_than_epoch
                .fetch_add(num_accounts, Ordering::Relaxed);
        }
    }

    /// return slot + offset, where offset can be +/-
    fn apply_offset_to_slot(slot: Slot, offset: i64) -> Slot {
        if offset > 0 {
            slot.saturating_add(offset as u64)
        } else {
            slot.saturating_sub(offset.unsigned_abs())
        }
    }

    /// Hash information about `storage` into `hasher`.
    ///
    /// # Parameters
    /// - `storage`: The storage to hash.
    /// - `slot`: The slot of the storage.
    /// - `hash_slot`: The slot at which the storage is being hashed.
    ///   Obsolete account data is only relevant for the hash if `hash_slot` is greater than the slot that marked the account obsolete.
    ///
    /// # Returns
    /// `true` if the storage is valid for loading from the cache.
    fn hash_storage_info(
        hasher: &mut impl StdHasher,
        storage: &AccountStorageEntry,
        slot: Slot,
        hash_slot: Slot,
    ) -> bool {
        // hash info about this storage
        storage.written_bytes().hash(hasher);

        // Obsolete accounts change the hash as they may cause accounts to no longer be included in the hash
        storage
            .get_obsolete_accounts(Some(hash_slot))
            .len()
            .hash(hasher);

        slot.hash(hasher);
        let storage_file = storage.accounts.path();
        storage_file.hash(hasher);
        let Ok(metadata) = std::fs::metadata(storage_file) else {
            return false;
        };
        let Ok(amod) = metadata.modified() else {
            return false;
        };
        let amod = amod
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        amod.hash(hasher);

        // if we made it here, we have hashed info and we should try to load from the cache
        true
    }

    pub fn calculate_accounts_hash_from(
        &self,
        data_source: CalcAccountsHashDataSource,
        slot: Slot,
        config: &CalcAccountsHashConfig<'_>,
    ) -> (AccountsHash, u64) {
        match data_source {
            CalcAccountsHashDataSource::Storages => {
                if self.accounts_cache.contains_any_slots(slot) {
                    // this indicates a race condition
                    inc_new_counter_info!("accounts_hash_items_in_write_cache", 1);
                }

                let mut collect_time = Measure::start("collect");
                let (combined_maps, slots) = self.get_storages(..=slot);
                collect_time.stop();

                let mut sort_time = Measure::start("sort_storages");
                let min_root = self.accounts_index.min_alive_root();
                let storages = SortedStorages::new_with_slots(
                    combined_maps.iter().zip(slots),
                    min_root,
                    Some(slot),
                );
                sort_time.stop();

                let mut timings = HashStats {
                    collect_snapshots_us: collect_time.as_us(),
                    storage_sort_us: sort_time.as_us(),
                    ..HashStats::default()
                };
                timings.calc_storage_size_quartiles(&combined_maps);

                self.calculate_accounts_hash(config, &storages, timings)
            }
            CalcAccountsHashDataSource::IndexForTests => {
                self.calculate_accounts_hash_from_index(slot, config)
            }
        }
    }

    fn calculate_accounts_hash_with_verify_from(
        &self,
        data_source: CalcAccountsHashDataSource,
        debug_verify: bool,
        slot: Slot,
        config: CalcAccountsHashConfig<'_>,
        expected_capitalization: Option<u64>,
    ) -> (AccountsHash, u64) {
        let (accounts_hash, total_lamports) =
            self.calculate_accounts_hash_from(data_source, slot, &config);
        if debug_verify {
            // calculate the other way (store or non-store) and verify results match.
            let data_source_other = match data_source {
                CalcAccountsHashDataSource::IndexForTests => CalcAccountsHashDataSource::Storages,
                CalcAccountsHashDataSource::Storages => CalcAccountsHashDataSource::IndexForTests,
            };
            let (accounts_hash_other, total_lamports_other) =
                self.calculate_accounts_hash_from(data_source_other, slot, &config);

            let success = accounts_hash == accounts_hash_other
                && total_lamports == total_lamports_other
                && total_lamports == expected_capitalization.unwrap_or(total_lamports);
            assert!(
                success,
                "calculate_accounts_hash_with_verify mismatch. hashes: {}, {}; lamports: {}, {}; \
                 expected lamports: {:?}, data source: {:?}, slot: {}",
                accounts_hash.0,
                accounts_hash_other.0,
                total_lamports,
                total_lamports_other,
                expected_capitalization,
                data_source,
                slot
            );
        }
        (accounts_hash, total_lamports)
    }

    /// run the accounts hash calculation and store the results
    #[allow(clippy::too_many_arguments)]
    pub fn update_accounts_hash_with_verify_from(
        &self,
        data_source: CalcAccountsHashDataSource,
        debug_verify: bool,
        slot: Slot,
        ancestors: &Ancestors,
        expected_capitalization: Option<u64>,
        epoch_schedule: &EpochSchedule,
        is_startup: bool,
    ) -> (AccountsHash, u64) {
        let epoch = epoch_schedule.get_epoch(slot);
        let (accounts_hash, total_lamports) = self.calculate_accounts_hash_with_verify_from(
            data_source,
            debug_verify,
            slot,
            CalcAccountsHashConfig {
                use_bg_thread_pool: !is_startup,
                ancestors: Some(ancestors),
                epoch_schedule,
                epoch,
                store_detailed_debug_info_on_failure: false,
            },
            expected_capitalization,
        );
        self.set_accounts_hash(slot, (accounts_hash, total_lamports));
        (accounts_hash, total_lamports)
    }

    /// Calculate the full accounts hash for `storages` and save the results at `slot`
    pub fn update_accounts_hash(
        &self,
        config: &CalcAccountsHashConfig<'_>,
        storages: &SortedStorages<'_>,
        slot: Slot,
        stats: HashStats,
    ) -> (AccountsHash, /*capitalization*/ u64) {
        let accounts_hash = self.calculate_accounts_hash(config, storages, stats);
        let old_accounts_hash = self.set_accounts_hash(slot, accounts_hash);
        if let Some(old_accounts_hash) = old_accounts_hash {
            warn!(
                "Accounts hash was already set for slot {slot}! old: {old_accounts_hash:?}, new: \
                 {accounts_hash:?}"
            );
        }
        accounts_hash
    }

    /// Calculate the incremental accounts hash for `storages` and save the results at `slot`
    pub fn update_incremental_accounts_hash(
        &self,
        config: &CalcAccountsHashConfig<'_>,
        storages: &SortedStorages<'_>,
        slot: Slot,
        stats: HashStats,
    ) -> (IncrementalAccountsHash, /*capitalization*/ u64) {
        let incremental_accounts_hash =
            self.calculate_incremental_accounts_hash(config, storages, stats);
        let old_incremental_accounts_hash =
            self.set_incremental_accounts_hash(slot, incremental_accounts_hash);
        if let Some(old_incremental_accounts_hash) = old_incremental_accounts_hash {
            warn!(
                "Incremental accounts hash was already set for slot {slot}! old: \
                 {old_incremental_accounts_hash:?}, new: {incremental_accounts_hash:?}"
            );
        }
        incremental_accounts_hash
    }

    /// Set the accounts hash for `slot`
    ///
    /// returns the previous accounts hash for `slot`
    #[cfg_attr(feature = "dev-context-only-utils", qualifiers(pub))]
    fn set_accounts_hash(
        &self,
        slot: Slot,
        accounts_hash: (AccountsHash, /*capitalization*/ u64),
    ) -> Option<(AccountsHash, /*capitalization*/ u64)> {
        self.accounts_hashes
            .lock()
            .unwrap()
            .insert(slot, accounts_hash)
    }

    /// After deserializing a snapshot, set the accounts hash for the new AccountsDb
    pub fn set_accounts_hash_from_snapshot(
        &mut self,
        slot: Slot,
        accounts_hash: SerdeAccountsHash,
        capitalization: u64,
    ) -> Option<(AccountsHash, /*capitalization*/ u64)> {
        self.set_accounts_hash(slot, (accounts_hash.into(), capitalization))
    }

    /// Get the accounts hash for `slot`
    pub fn get_accounts_hash(&self, slot: Slot) -> Option<(AccountsHash, /*capitalization*/ u64)> {
        self.accounts_hashes.lock().unwrap().get(&slot).cloned()
    }

    /// Get all accounts hashes
    pub fn get_accounts_hashes(&self) -> HashMap<Slot, (AccountsHash, /*capitalization*/ u64)> {
        self.accounts_hashes.lock().unwrap().clone()
    }

    /// Set the incremental accounts hash for `slot`
    ///
    /// returns the previous incremental accounts hash for `slot`
    pub fn set_incremental_accounts_hash(
        &self,
        slot: Slot,
        incremental_accounts_hash: (IncrementalAccountsHash, /*capitalization*/ u64),
    ) -> Option<(IncrementalAccountsHash, /*capitalization*/ u64)> {
        self.incremental_accounts_hashes
            .lock()
            .unwrap()
            .insert(slot, incremental_accounts_hash)
    }

    /// After deserializing a snapshot, set the incremental accounts hash for the new AccountsDb
    pub fn set_incremental_accounts_hash_from_snapshot(
        &mut self,
        slot: Slot,
        incremental_accounts_hash: SerdeIncrementalAccountsHash,
        capitalization: u64,
    ) -> Option<(IncrementalAccountsHash, /*capitalization*/ u64)> {
        self.set_incremental_accounts_hash(slot, (incremental_accounts_hash.into(), capitalization))
    }

    /// Get the incremental accounts hash for `slot`
    pub fn get_incremental_accounts_hash(
        &self,
        slot: Slot,
    ) -> Option<(IncrementalAccountsHash, /*capitalization*/ u64)> {
        self.incremental_accounts_hashes
            .lock()
            .unwrap()
            .get(&slot)
            .cloned()
    }

    /// Get all incremental accounts hashes
    pub fn get_incremental_accounts_hashes(
        &self,
    ) -> HashMap<Slot, (IncrementalAccountsHash, /*capitalization*/ u64)> {
        self.incremental_accounts_hashes.lock().unwrap().clone()
    }

    /// Purge accounts hashes that are older than `latest_full_snapshot_slot`
    ///
    /// Should only be called by AccountsHashVerifier, since it consumes the accounts hashes and
    /// knows which ones are still needed.
    pub fn purge_old_accounts_hashes(&self, latest_full_snapshot_slot: Slot) {
        self.accounts_hashes
            .lock()
            .unwrap()
            .retain(|&slot, _| slot >= latest_full_snapshot_slot);
        self.incremental_accounts_hashes
            .lock()
            .unwrap()
            .retain(|&slot, _| slot >= latest_full_snapshot_slot);
    }

    fn sort_slot_storage_scan(accum: &mut BinnedHashData) -> u64 {
        let (_, sort_time) = measure_us!(accum.iter_mut().for_each(|items| {
            // sort_by vs unstable because slot and write_version are already in order
            items.sort_by(AccountsHasher::compare_two_hash_entries);
        }));
        sort_time
    }

    /// normal code path returns the common cache path
    /// when called after a failure has been detected, redirect the cache storage to a separate folder for debugging later
    fn get_cache_hash_data(
        accounts_hash_cache_path: PathBuf,
        config: &CalcAccountsHashConfig<'_>,
        kind: CalcAccountsHashKind,
        slot: Slot,
        storages_start_slot: Slot,
    ) -> CacheHashData {
        let accounts_hash_cache_path = if !config.store_detailed_debug_info_on_failure {
            accounts_hash_cache_path
        } else {
            // this path executes when we are failing with a hash mismatch
            let failed_dir = accounts_hash_cache_path
                .join("failed_calculate_accounts_hash_cache")
                .join(slot.to_string());
            _ = std::fs::remove_dir_all(&failed_dir);
            failed_dir
        };
        let deletion_policy = match kind {
            CalcAccountsHashKind::Full => CacheHashDeletionPolicy::AllUnused,
            CalcAccountsHashKind::Incremental => {
                CacheHashDeletionPolicy::UnusedAtLeast(storages_start_slot)
            }
        };
        CacheHashData::new(accounts_hash_cache_path, deletion_policy)
    }

    /// Calculate the full accounts hash
    ///
    /// This is intended to be used by startup verification, and also AccountsHashVerifier.
    /// Uses account storage files as the data source for the calculation.
    pub fn calculate_accounts_hash(
        &self,
        config: &CalcAccountsHashConfig<'_>,
        storages: &SortedStorages<'_>,
        stats: HashStats,
    ) -> (AccountsHash, u64) {
        let (accounts_hash, capitalization) = self.calculate_accounts_hash_from_storages(
            config,
            storages,
            stats,
            CalcAccountsHashKind::Full,
        );
        let AccountsHashKind::Full(accounts_hash) = accounts_hash else {
            panic!("calculate_accounts_hash_from_storages must return a FullAccountsHash");
        };
        (accounts_hash, capitalization)
    }

    /// Calculate the incremental accounts hash
    ///
    /// This calculation is intended to be used by incremental snapshots, and thus differs from a
    /// "full" accounts hash in a few ways:
    /// - Zero-lamport accounts are *included* in the hash because zero-lamport accounts are also
    ///   included in the incremental snapshot.  This ensures reconstructing the AccountsDb is
    ///   still correct when using this incremental accounts hash.
    /// - `storages` must be the same as the ones going into the incremental snapshot.
    pub fn calculate_incremental_accounts_hash(
        &self,
        config: &CalcAccountsHashConfig<'_>,
        storages: &SortedStorages<'_>,
        stats: HashStats,
    ) -> (IncrementalAccountsHash, /* capitalization */ u64) {
        let (accounts_hash, capitalization) = self.calculate_accounts_hash_from_storages(
            config,
            storages,
            stats,
            CalcAccountsHashKind::Incremental,
        );
        let AccountsHashKind::Incremental(incremental_accounts_hash) = accounts_hash else {
            panic!("calculate_incremental_accounts_hash must return an IncrementalAccountsHash");
        };
        (incremental_accounts_hash, capitalization)
    }

    /// The shared code for calculating accounts hash from storages.
    /// Used for both full accounts hash and incremental accounts hash calculation.
    fn calculate_accounts_hash_from_storages(
        &self,
        config: &CalcAccountsHashConfig<'_>,
        storages: &SortedStorages<'_>,
        mut stats: HashStats,
        kind: CalcAccountsHashKind,
    ) -> (AccountsHashKind, u64) {
        let total_time = Measure::start("");
        let _guard = self.active_stats.activate(ActiveStatItem::Hash);
        let storages_start_slot = storages.range().start;
        stats.oldest_root = storages_start_slot;

        let slot = storages.max_slot_inclusive();
        let use_bg_thread_pool = config.use_bg_thread_pool;
        let accounts_hash_cache_path = self.accounts_hash_cache_path.clone();
        let transient_accounts_hash_cache_dir = TempDir::new_in(&accounts_hash_cache_path)
            .expect("create transient accounts hash cache dir");
        let transient_accounts_hash_cache_path =
            transient_accounts_hash_cache_dir.path().to_path_buf();
        let scan_and_hash = || {
            let (cache_hash_data, cache_hash_data_us) = measure_us!(Self::get_cache_hash_data(
                accounts_hash_cache_path,
                config,
                kind,
                slot,
                storages_start_slot,
            ));
            stats.cache_hash_data_us += cache_hash_data_us;

            let bounds = Range {
                start: 0,
                end: self.hash_calculation_pubkey_bins,
            };

            let accounts_hasher = AccountsHasher {
                zero_lamport_accounts: kind.zero_lamport_accounts(),
                dir_for_temp_cache_files: transient_accounts_hash_cache_path,
                active_stats: &self.active_stats,
            };

            // get raw data by scanning
            let cache_hash_data_file_references = self.scan_snapshot_stores_with_cache(
                &cache_hash_data,
                storages,
                &mut stats,
                self.hash_calculation_pubkey_bins,
                &bounds,
                config,
            );

            let cache_hash_data_files = cache_hash_data_file_references
                .iter()
                .map(|d| d.map())
                .collect::<Vec<_>>();

            if let Some(err) = cache_hash_data_files
                .iter()
                .filter_map(|r| r.as_ref().err())
                .next()
            {
                panic!("failed generating accounts hash files: {err:?}");
            }

            // convert mmapped cache files into slices of data
            let cache_hash_intermediates = cache_hash_data_files
                .iter()
                .map(|d| d.as_ref().unwrap().get_cache_hash_data())
                .collect::<Vec<_>>();

            // turn raw data into merkle tree hashes and sum of lamports
            let (accounts_hash, capitalization) = accounts_hasher.rest_of_hash_calculation(
                &cache_hash_intermediates,
                self.hash_calculation_pubkey_bins,
                &mut stats,
            );
            let accounts_hash = match kind {
                CalcAccountsHashKind::Full => AccountsHashKind::Full(AccountsHash(accounts_hash)),
                CalcAccountsHashKind::Incremental => {
                    AccountsHashKind::Incremental(IncrementalAccountsHash(accounts_hash))
                }
            };
            info!(
                "calculate_accounts_hash_from_storages: slot: {slot}, {accounts_hash:?}, \
                 capitalization: {capitalization}"
            );
            (accounts_hash, capitalization)
        };

        let result = if use_bg_thread_pool {
            self.thread_pool_hash.install(scan_and_hash)
        } else {
            scan_and_hash()
        };
        stats.total_us = total_time.end_as_us();
        stats.log();
        result
    }

    /// Verify accounts hash at startup (or tests)
    ///
    /// Calculate accounts hash(es) and compare them to the values set at startup.
    /// If `base` is `None`, only calculates the full accounts hash for `[0, slot]`.
    /// If `base` is `Some`, calculate the full accounts hash for `[0, base slot]`
    /// and then calculate the incremental accounts hash for `(base slot, slot]`.
    pub fn verify_accounts_hash_and_lamports(
        &self,
        snapshot_storages_and_slots: (&[Arc<AccountStorageEntry>], &[Slot]),
        slot: Slot,
        total_lamports: u64,
        base: Option<(Slot, /*capitalization*/ u64)>,
        config: VerifyAccountsHashAndLamportsConfig,
    ) -> Result<(), AccountsHashVerificationError> {
        let calc_config = CalcAccountsHashConfig {
            use_bg_thread_pool: config.use_bg_thread_pool,
            ancestors: Some(config.ancestors),
            epoch_schedule: config.epoch_schedule,
            epoch: config.epoch,
            store_detailed_debug_info_on_failure: config.store_detailed_debug_info,
        };
        let hash_mismatch_is_error = !config.ignore_mismatch;

        if let Some((base_slot, base_capitalization)) = base {
            self.verify_accounts_hash_and_lamports(
                snapshot_storages_and_slots,
                base_slot,
                base_capitalization,
                None,
                config,
            )?;

            let storages_and_slots = snapshot_storages_and_slots
                .0
                .iter()
                .zip(snapshot_storages_and_slots.1.iter())
                .filter(|storage_and_slot| *storage_and_slot.1 > base_slot)
                .map(|(storage, slot)| (storage, *slot));
            let sorted_storages = SortedStorages::new_with_slots(storages_and_slots, None, None);
            let calculated_incremental_accounts_hash = self.calculate_incremental_accounts_hash(
                &calc_config,
                &sorted_storages,
                HashStats::default(),
            );
            let found_incremental_accounts_hash = self
                .get_incremental_accounts_hash(slot)
                .ok_or(AccountsHashVerificationError::MissingAccountsHash)?;
            if calculated_incremental_accounts_hash != found_incremental_accounts_hash {
                warn!(
                    "mismatched incremental accounts hash for slot {slot}: \
                     {calculated_incremental_accounts_hash:?} (calculated) != \
                     {found_incremental_accounts_hash:?} (expected)"
                );
                if hash_mismatch_is_error {
                    return Err(AccountsHashVerificationError::MismatchedAccountsHash);
                }
            }
        } else {
            let storages_and_slots = snapshot_storages_and_slots
                .0
                .iter()
                .zip(snapshot_storages_and_slots.1.iter())
                .filter(|storage_and_slot| *storage_and_slot.1 <= slot)
                .map(|(storage, slot)| (storage, *slot));
            let sorted_storages = SortedStorages::new_with_slots(storages_and_slots, None, None);
            let (calculated_accounts_hash, calculated_lamports) =
                self.calculate_accounts_hash(&calc_config, &sorted_storages, HashStats::default());
            if calculated_lamports != total_lamports {
                warn!(
                    "Mismatched total lamports: {total_lamports} calculated: {calculated_lamports}"
                );
                return Err(AccountsHashVerificationError::MismatchedTotalLamports(
                    calculated_lamports,
                    total_lamports,
                ));
            }
            let (found_accounts_hash, _) = self
                .get_accounts_hash(slot)
                .ok_or(AccountsHashVerificationError::MissingAccountsHash)?;
            if calculated_accounts_hash != found_accounts_hash {
                warn!(
                    "Mismatched accounts hash for slot {slot}: {calculated_accounts_hash:?} \
                     (calculated) != {found_accounts_hash:?} (expected)"
                );
                if hash_mismatch_is_error {
                    return Err(AccountsHashVerificationError::MismatchedAccountsHash);
                }
            }
        }

        Ok(())
    }

    /// Returns all of the accounts' pubkeys for a given slot
    pub fn get_pubkeys_for_slot(&self, slot: Slot) -> Vec<Pubkey> {
        let scan_result = self.scan_cache_storage_fallback(
            slot,
            |loaded_account| Some(*loaded_account.pubkey()),
            |accum: &mut HashSet<Pubkey>, storage| {
                storage
                    .scan_pubkeys(|pubkey| {
                        accum.insert(*pubkey);
                    })
                    .expect("must scan accounts storage");
            },
        );
        match scan_result {
            ScanStorageResult::Cached(cached_result) => cached_result,
            ScanStorageResult::Stored(stored_result) => stored_result.into_iter().collect(),
        }
    }
    /// helper to return
    /// 1. pubkey, hash pairs for the slot
    /// 2. us spent scanning
    /// 3. Measure started when we began accumulating
    pub fn get_pubkey_hash_for_slot(
        &self,
        slot: Slot,
    ) -> (Vec<(Pubkey, AccountHash)>, u64, Measure) {
        let mut scan = Measure::start("scan");
        let scan_result: ScanStorageResult<(Pubkey, AccountHash), HashMap<Pubkey, AccountHash>> =
            self.scan_account_storage(
                slot,
                |loaded_account| {
                    // Cache only has one version per key, don't need to worry about versioning
                    Some((*loaded_account.pubkey(), loaded_account.loaded_hash()))
                },
                |accum: &mut HashMap<_, _>, stored_account, data| {
                    // SAFETY: We called scan_account_storage() with
                    // ScanAccountStorageData::DataRefForStorage, so `data` must be Some.
                    let data = data.unwrap();
                    let loaded_account =
                        LoadedAccount::Stored(StoredAccountInfo::new_from(stored_account, data));
                    let mut loaded_hash = loaded_account.loaded_hash();
                    if loaded_hash == AccountHash(Hash::default()) {
                        loaded_hash = Self::hash_account(&loaded_account, loaded_account.pubkey())
                    }
                    accum.insert(*loaded_account.pubkey(), loaded_hash);
                },
                ScanAccountStorageData::DataRefForStorage,
            );
        scan.stop();

        let accumulate = Measure::start("accumulate");
        let hashes: Vec<_> = match scan_result {
            ScanStorageResult::Cached(cached_result) => cached_result,
            ScanStorageResult::Stored(stored_result) => stored_result.into_iter().collect(),
        };

        (hashes, scan.as_us(), accumulate)
    }

    /// Return all of the accounts for a given slot
    pub fn get_pubkey_account_for_slot(&self, slot: Slot) -> Vec<(Pubkey, AccountSharedData)> {
        let scan_result = self.scan_account_storage(
            slot,
            |loaded_account| {
                // Cache only has one version per key, don't need to worry about versioning
                Some((*loaded_account.pubkey(), loaded_account.take_account()))
            },
            |accum: &mut HashMap<_, _>, stored_account, data| {
                // SAFETY: We called scan_account_storage() with
                // ScanAccountStorageData::DataRefForStorage, so `data` must be Some.
                let data = data.unwrap();
                let loaded_account =
                    LoadedAccount::Stored(StoredAccountInfo::new_from(stored_account, data));
                // Storage may have duplicates so only keep the latest version for each key
                accum.insert(*loaded_account.pubkey(), loaded_account.take_account());
            },
            ScanAccountStorageData::DataRefForStorage,
        );

        match scan_result {
            ScanStorageResult::Cached(cached_result) => cached_result,
            ScanStorageResult::Stored(stored_result) => stored_result.into_iter().collect(),
        }
    }

    /// Return all of the accounts for a given slot
    pub fn get_pubkey_hash_account_for_slot(&self, slot: Slot) -> Vec<PubkeyHashAccount> {
        type ScanResult =
            ScanStorageResult<PubkeyHashAccount, HashMap<Pubkey, (AccountHash, AccountSharedData)>>;
        let scan_result: ScanResult = self.scan_account_storage(
            slot,
            |loaded_account| {
                // Cache only has one version per key, don't need to worry about versioning
                Some(PubkeyHashAccount {
                    pubkey: *loaded_account.pubkey(),
                    hash: loaded_account.loaded_hash(),
                    account: loaded_account.take_account(),
                })
            },
            |accum: &mut HashMap<_, _>, stored_account, data| {
                // SAFETY: We called scan_account_storage() with
                // ScanAccountStorageData::DataRefForStorage, so `data` must be Some.
                let data = data.unwrap();
                let loaded_account =
                    LoadedAccount::Stored(StoredAccountInfo::new_from(stored_account, data));
                let mut loaded_hash = loaded_account.loaded_hash();
                let key = *loaded_account.pubkey();
                let account = loaded_account.take_account();
                if loaded_hash == AccountHash(Hash::default()) {
                    loaded_hash = Self::hash_account(&account, &key)
                }
                // Storage may have duplicates so only keep the latest version for each key
                accum.insert(key, (loaded_hash, account));
            },
            ScanAccountStorageData::DataRefForStorage,
        );

        match scan_result {
            ScanStorageResult::Cached(cached_result) => cached_result,
            ScanStorageResult::Stored(stored_result) => stored_result
                .into_iter()
                .map(|(pubkey, (hash, account))| PubkeyHashAccount {
                    pubkey,
                    hash,
                    account,
                })
                .collect(),
        }
    }

    /// Calculate accounts delta hash for `slot`
    pub fn calculate_accounts_delta_hash_internal(
        &self,
        slot: Slot,
        ignore: Option<Pubkey>,
    ) -> AccountsDeltaHash {
        let (mut hashes, scan_us, mut accumulate) = self.get_pubkey_hash_for_slot(slot);

        if let Some(ignore) = ignore {
            hashes.retain(|k| k.0 != ignore);
        }

        let accounts_delta_hash = self
            .thread_pool
            .install(|| AccountsDeltaHash(AccountsHasher::accumulate_account_hashes(hashes)));
        accumulate.stop();

        self.set_accounts_delta_hash(slot, accounts_delta_hash);

        self.stats
            .delta_hash_scan_time_total_us
            .fetch_add(scan_us, Ordering::Relaxed);
        self.stats
            .delta_hash_accumulate_time_total_us
            .fetch_add(accumulate.as_us(), Ordering::Relaxed);
        self.stats.delta_hash_num.fetch_add(1, Ordering::Relaxed);

        accounts_delta_hash
    }

    /// Set the accounts delta hash for `slot` in the `accounts_delta_hashes` map
    ///
    /// returns the previous accounts delta hash for `slot`
    #[cfg_attr(feature = "dev-context-only-utils", qualifiers(pub))]
    fn set_accounts_delta_hash(
        &self,
        slot: Slot,
        accounts_delta_hash: AccountsDeltaHash,
    ) -> Option<AccountsDeltaHash> {
        self.accounts_delta_hashes
            .lock()
            .unwrap()
            .insert(slot, accounts_delta_hash)
    }

    /// After deserializing a snapshot, set the accounts delta hash for the new AccountsDb
    pub fn set_accounts_delta_hash_from_snapshot(
        &mut self,
        slot: Slot,
        accounts_delta_hash: SerdeAccountsDeltaHash,
    ) -> Option<AccountsDeltaHash> {
        self.set_accounts_delta_hash(slot, accounts_delta_hash.into())
    }

    /// Get the accounts delta hash for `slot` in the `accounts_delta_hashes` map
    pub fn get_accounts_delta_hash(&self, slot: Slot) -> Option<AccountsDeltaHash> {
        self.accounts_delta_hashes
            .lock()
            .unwrap()
            .get(&slot)
            .cloned()
    }

    fn update_index<'a>(
        &self,
        infos: Vec<AccountInfo>,
        accounts: &impl StorableAccounts<'a>,
        reclaim: UpsertReclaim,
        update_index_thread_selection: UpdateIndexThreadSelection,
        thread_pool: &ThreadPool,
    ) -> SlotList<AccountInfo> {
        let target_slot = accounts.target_slot();
        let len = std::cmp::min(accounts.len(), infos.len());

        let update = |start, end| {
            let mut reclaims = Vec::with_capacity((end - start) / 2);

            (start..end).for_each(|i| {
                let info = infos[i];
                accounts.account(i, |account| {
                    let old_slot = accounts.slot(i);
                    self.accounts_index.upsert(
                        target_slot,
                        old_slot,
                        account.pubkey(),
                        &account,
                        &self.account_indexes,
                        info,
                        &mut reclaims,
                        reclaim,
                    );
                });
            });
            reclaims
        };

        let threshold = 1;
        if matches!(
            update_index_thread_selection,
            UpdateIndexThreadSelection::PoolWithThreshold,
        ) && len > threshold
        {
            let chunk_size = std::cmp::max(1, len / quarter_thread_count()); // # pubkeys/thread
            let batches = 1 + len / chunk_size;
            thread_pool.install(|| {
                (0..batches)
                    .into_par_iter()
                    .map(|batch| {
                        let start = batch * chunk_size;
                        let end = std::cmp::min(start + chunk_size, len);
                        update(start, end)
                    })
                    .flatten()
                    .collect::<Vec<_>>()
            })
        } else {
            update(0, len)
        }
    }

    fn should_not_shrink(alive_bytes: u64, total_bytes: u64) -> bool {
        alive_bytes >= total_bytes
    }

    fn is_shrinking_productive(store: &AccountStorageEntry) -> bool {
        let alive_count = store.count();
        let total_bytes = store.capacity();
        let alive_bytes = store.alive_bytes_exclude_zero_lamport_single_ref_accounts() as u64;
        if Self::should_not_shrink(alive_bytes, total_bytes) {
            trace!(
                "shrink_slot_forced ({}): not able to shrink at all: num alive: {}, bytes alive: \
                 {}, bytes total: {}, bytes saved: {}",
                store.slot(),
                alive_count,
                alive_bytes,
                total_bytes,
                total_bytes.saturating_sub(alive_bytes),
            );
            return false;
        }

        true
    }

    /// Determines whether a given AccountStorageEntry instance is a
    /// candidate for shrinking.
    pub(crate) fn is_candidate_for_shrink(&self, store: &AccountStorageEntry) -> bool {
        // appended ancient append vecs should not be shrunk by the normal shrink codepath.
        // It is not possible to identify ancient append vecs when we pack, so no check for ancient when we are not appending.
        let total_bytes = store.capacity();

        let alive_bytes = store.alive_bytes_exclude_zero_lamport_single_ref_accounts() as u64;
        match self.shrink_ratio {
            AccountShrinkThreshold::TotalSpace { shrink_ratio: _ } => alive_bytes < total_bytes,
            AccountShrinkThreshold::IndividualStore { shrink_ratio } => {
                (alive_bytes as f64 / total_bytes as f64) < shrink_ratio
            }
        }
    }

    /// returns (dead slots, reclaimed_offsets)
    fn remove_dead_accounts<'a, I>(
        &'a self,
        reclaims: I,
        expected_slot: Option<Slot>,
        mark_accounts_obsolete: MarkAccountsObsolete,
    ) -> (IntSet<Slot>, SlotOffsets)
    where
        I: Iterator<Item = &'a (Slot, AccountInfo)>,
    {
        let mut reclaimed_offsets = SlotOffsets::default();

        assert!(self.storage.no_shrink_in_progress());

        let mut dead_slots = IntSet::default();
        let mut new_shrink_candidates = ShrinkCandidates::default();
        let mut measure = Measure::start("remove");
        for (slot, account_info) in reclaims {
            // No cached accounts should make it here
            assert!(!account_info.is_cached());
            reclaimed_offsets
                .entry(*slot)
                .or_default()
                .insert(account_info.offset());
        }
        if let Some(expected_slot) = expected_slot {
            assert_eq!(reclaimed_offsets.len(), 1);
            assert!(reclaimed_offsets.contains_key(&expected_slot));
        }

        self.clean_accounts_stats
            .slots_cleaned
            .fetch_add(reclaimed_offsets.len() as u64, Ordering::Relaxed);

        reclaimed_offsets.iter().for_each(|(slot, offsets)| {
            if let Some(store) = self.storage.get_slot_storage_entry(*slot) {
                assert_eq!(
                    *slot,
                    store.slot(),
                    "AccountsDB::accounts_index corrupted. Storage pointed to: {}, expected: {}, \
                     should only point to one slot",
                    store.slot(),
                    *slot
                );

                let remaining_accounts = if offsets.len() == store.count() {
                    // all remaining alive accounts in the storage are being removed, so the entire storage/slot is dead
                    store.remove_accounts(store.alive_bytes(), offsets.len())
                } else {
                    // not all accounts are being removed, so figure out sizes of accounts we are removing and update the alive bytes and alive account count
                    let (remaining_accounts, us) = measure_us!({
                        let mut offsets = offsets.iter().cloned().collect::<Vec<_>>();
                        // sort so offsets are in order. This improves efficiency of loading the accounts.
                        offsets.sort_unstable();
                        let data_lens = store.accounts.get_account_data_lens(&offsets);
                        let dead_bytes = data_lens
                            .iter()
                            .map(|len| store.accounts.calculate_stored_size(*len))
                            .sum();
                        let remaining_accounts = store.remove_accounts(dead_bytes, offsets.len());

                        if let MarkAccountsObsolete::Yes(slot_marked_obsolete) =
                            mark_accounts_obsolete
                        {
                            store.mark_accounts_obsolete(
                                offsets.into_iter().zip(data_lens),
                                slot_marked_obsolete,
                            );
                        }
                        remaining_accounts
                    });
                    self.clean_accounts_stats
                        .get_account_sizes_us
                        .fetch_add(us, Ordering::Relaxed);
                    remaining_accounts
                };

                // Check if we have removed all accounts from the storage
                // This may be different from the check above as this
                // can be multithreaded
                if remaining_accounts == 0 {
                    self.dirty_stores.insert(*slot, store);
                    dead_slots.insert(*slot);
                } else if Self::is_shrinking_productive(&store)
                    && self.is_candidate_for_shrink(&store)
                {
                    // Checking that this single storage entry is ready for shrinking,
                    // should be a sufficient indication that the slot is ready to be shrunk
                    // because slots should only have one storage entry, namely the one that was
                    // created by `flush_slot_cache()`.
                    new_shrink_candidates.insert(*slot);
                };
            }
        });
        measure.stop();
        self.clean_accounts_stats
            .remove_dead_accounts_remove_us
            .fetch_add(measure.as_us(), Ordering::Relaxed);

        let mut measure = Measure::start("shrink");
        let mut shrink_candidate_slots = self.shrink_candidate_slots.lock().unwrap();
        for slot in new_shrink_candidates {
            shrink_candidate_slots.insert(slot);
        }
        drop(shrink_candidate_slots);
        measure.stop();
        self.clean_accounts_stats
            .remove_dead_accounts_shrink_us
            .fetch_add(measure.as_us(), Ordering::Relaxed);

        dead_slots.retain(|slot| {
            if let Some(slot_store) = self.storage.get_slot_storage_entry(*slot) {
                if slot_store.count() != 0 {
                    return false;
                }
            }
            true
        });

        (dead_slots, reclaimed_offsets)
    }

    fn remove_dead_slots_metadata<'a>(
        &'a self,
        dead_slots_iter: impl Iterator<Item = &'a Slot> + Clone,
    ) {
        let mut measure = Measure::start("remove_dead_slots_metadata-ms");
        self.clean_dead_slots_from_accounts_index(dead_slots_iter.clone());

        let mut accounts_delta_hashes = self.accounts_delta_hashes.lock().unwrap();
        for slot in dead_slots_iter {
            accounts_delta_hashes.remove(slot);
        }
        drop(accounts_delta_hashes);

        measure.stop();
        inc_new_counter_info!("remove_dead_slots_metadata-ms", measure.as_ms() as usize);
    }

    /// lookup each pubkey in 'pubkeys' and unref it in the accounts index
    /// skip pubkeys that are in 'pubkeys_removed_from_accounts_index'
    fn unref_pubkeys<'a>(
        &'a self,
        pubkeys: impl Iterator<Item = &'a Pubkey> + Clone + Send + Sync,
        num_pubkeys: usize,
        pubkeys_removed_from_accounts_index: &'a PubkeysRemovedFromAccountsIndex,
    ) {
        let batches = 1 + (num_pubkeys / UNREF_ACCOUNTS_BATCH_SIZE);
        self.thread_pool_clean.install(|| {
            (0..batches).into_par_iter().for_each(|batch| {
                let skip = batch * UNREF_ACCOUNTS_BATCH_SIZE;
                self.accounts_index.scan(
                    pubkeys
                        .clone()
                        .skip(skip)
                        .take(UNREF_ACCOUNTS_BATCH_SIZE)
                        .filter(|pubkey| {
                            // filter out pubkeys that have already been removed from the accounts index in a previous step
                            let already_removed =
                                pubkeys_removed_from_accounts_index.contains(pubkey);
                            !already_removed
                        }),
                    |_pubkey, slots_refs, _entry| {
                        if let Some((slot_list, ref_count)) = slots_refs {
                            // Let's handle the special case - after unref, the result is a single ref zero lamport account.
                            if slot_list.len() == 1 && ref_count == 2 {
                                if let Some((slot_alive, acct_info)) = slot_list.first() {
                                    if acct_info.is_zero_lamport() && !acct_info.is_cached() {
                                        self.zero_lamport_single_ref_found(
                                            *slot_alive,
                                            acct_info.offset(),
                                        );
                                    }
                                }
                            }
                        }
                        AccountsIndexScanResult::Unref
                    },
                    None,
                    false,
                    ScanFilter::All,
                )
            });
        });
    }

    /// lookup each pubkey in 'purged_slot_pubkeys' and unref it in the accounts index
    /// populate 'purged_stored_account_slots' by grouping 'purged_slot_pubkeys' by pubkey
    /// pubkeys_removed_from_accounts_index - These keys have already been removed from the accounts index
    ///    and should not be unref'd. If they exist in the accounts index, they are NEW.
    fn unref_accounts(
        &self,
        purged_slot_pubkeys: HashSet<(Slot, Pubkey)>,
        purged_stored_account_slots: &mut AccountSlots,
        pubkeys_removed_from_accounts_index: &PubkeysRemovedFromAccountsIndex,
    ) {
        self.unref_pubkeys(
            purged_slot_pubkeys.iter().map(|(_slot, pubkey)| pubkey),
            purged_slot_pubkeys.len(),
            pubkeys_removed_from_accounts_index,
        );
        for (slot, pubkey) in purged_slot_pubkeys {
            purged_stored_account_slots
                .entry(pubkey)
                .or_default()
                .insert(slot);
        }
    }

    fn clean_dead_slots_from_accounts_index<'a>(
        &'a self,
        dead_slots_iter: impl Iterator<Item = &'a Slot> + Clone,
    ) {
        let mut accounts_index_root_stats = AccountsIndexRootsStats::default();
        let mut measure = Measure::start("clean_dead_slot");
        let mut rooted_cleaned_count = 0;
        let mut unrooted_cleaned_count = 0;
        let dead_slots: Vec<_> = dead_slots_iter
            .map(|slot| {
                if self.accounts_index.clean_dead_slot(*slot) {
                    rooted_cleaned_count += 1;
                } else {
                    unrooted_cleaned_count += 1;
                }
                *slot
            })
            .collect();
        measure.stop();
        accounts_index_root_stats.clean_dead_slot_us += measure.as_us();
        if self.log_dead_slots.load(Ordering::Relaxed) {
            info!(
                "remove_dead_slots_metadata: {} dead slots",
                dead_slots.len()
            );
            trace!("remove_dead_slots_metadata: dead_slots: {dead_slots:?}");
        }
        self.accounts_index
            .update_roots_stats(&mut accounts_index_root_stats);
        accounts_index_root_stats.rooted_cleaned_count += rooted_cleaned_count;
        accounts_index_root_stats.unrooted_cleaned_count += unrooted_cleaned_count;

        self.clean_accounts_stats
            .latest_accounts_index_roots_stats
            .update(&accounts_index_root_stats);
    }

    /// pubkeys_removed_from_accounts_index - These keys have already been removed from the accounts index
    ///    and should not be unref'd. If they exist in the accounts index, they are NEW.
    fn clean_stored_dead_slots(
        &self,
        dead_slots: &IntSet<Slot>,
        purged_account_slots: Option<&mut AccountSlots>,
        pubkeys_removed_from_accounts_index: &PubkeysRemovedFromAccountsIndex,
    ) {
        let mut measure = Measure::start("clean_stored_dead_slots-ms");
        let mut stores = vec![];
        // get all stores in a vec so we can iterate in parallel
        for slot in dead_slots.iter() {
            if let Some(slot_storage) = self.storage.get_slot_storage_entry(*slot) {
                stores.push(slot_storage);
            }
        }
        // get all pubkeys in all dead slots
        let purged_slot_pubkeys: HashSet<(Slot, Pubkey)> = {
            self.thread_pool_clean.install(|| {
                stores
                    .into_par_iter()
                    .map(|store| {
                        let slot = store.slot();
                        let mut pubkeys = Vec::with_capacity(store.count());
                        // Obsolete accounts are already unreffed before this point, so do not add
                        // them to the pubkeys list.
                        let obsolete_accounts = store.get_obsolete_accounts(None);
                        store
                            .accounts
                            .scan_accounts_without_data(|offset, account| {
                                if !obsolete_accounts.contains(&(offset, account.data_len)) {
                                    pubkeys.push((slot, *account.pubkey));
                                }
                            })
                            .expect("must scan accounts storage");
                        pubkeys
                    })
                    .flatten()
                    .collect::<HashSet<_>>()
            })
        };

        //Unref the accounts from storage
        let mut accounts_index_root_stats = AccountsIndexRootsStats::default();
        let mut measure_unref = Measure::start("unref_from_storage");

        if let Some(purged_account_slots) = purged_account_slots {
            self.unref_accounts(
                purged_slot_pubkeys,
                purged_account_slots,
                pubkeys_removed_from_accounts_index,
            );
        }
        measure_unref.stop();
        accounts_index_root_stats.clean_unref_from_storage_us += measure_unref.as_us();

        self.clean_accounts_stats
            .latest_accounts_index_roots_stats
            .update(&accounts_index_root_stats);

        self.remove_dead_slots_metadata(dead_slots.iter());
        measure.stop();
        self.clean_accounts_stats
            .clean_stored_dead_slots_us
            .fetch_add(measure.as_us(), Ordering::Relaxed);
    }

    pub fn store_cached<'a>(&self, accounts: impl StorableAccounts<'a>) {
        self.store(
            accounts,
            None,
            UpdateIndexThreadSelection::PoolWithThreshold,
        );
    }

    pub(crate) fn store_cached_inline_update_index<'a>(
        &self,
        accounts: impl StorableAccounts<'a>,
        transactions: Option<&'a [&'a SanitizedTransaction]>,
    ) {
        self.store(accounts, transactions, UpdateIndexThreadSelection::Inline);
    }

    fn store<'a>(
        &self,
        accounts: impl StorableAccounts<'a>,
        transactions: Option<&'a [&'a SanitizedTransaction]>,
        update_index_thread_selection: UpdateIndexThreadSelection,
    ) {
        // If all transactions in a batch are errored,
        // it's possible to get a store with no accounts.
        if accounts.is_empty() {
            return;
        }

        let mut total_data = 0;
        (0..accounts.len()).for_each(|index| {
            total_data += accounts.data_len(index);
        });

        self.stats
            .store_total_data
            .fetch_add(total_data as u64, Ordering::Relaxed);

        self.store_accounts_unfrozen(accounts, transactions, update_index_thread_selection);
        self.report_store_timings();
    }

    fn report_store_timings(&self) {
        if self.stats.last_store_report.should_update(1000) {
            let read_cache_stats = self.read_only_accounts_cache.get_and_reset_stats();
            datapoint_info!(
                "accounts_db_store_timings",
                (
                    "hash_accounts",
                    self.stats.store_hash_accounts.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "store_accounts",
                    self.stats.store_accounts.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "update_index",
                    self.stats.store_update_index.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "handle_reclaims",
                    self.stats.store_handle_reclaims.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "append_accounts",
                    self.stats.store_append_accounts.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "stakes_cache_check_and_store_us",
                    self.stats
                        .stakes_cache_check_and_store_us
                        .swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "num_accounts",
                    self.stats.store_num_accounts.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "total_data",
                    self.stats.store_total_data.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "read_only_accounts_cache_entries",
                    self.read_only_accounts_cache.cache_len(),
                    i64
                ),
                (
                    "read_only_accounts_cache_data_size",
                    self.read_only_accounts_cache.data_size(),
                    i64
                ),
                ("read_only_accounts_cache_hits", read_cache_stats.hits, i64),
                (
                    "read_only_accounts_cache_misses",
                    read_cache_stats.misses,
                    i64
                ),
                (
                    "read_only_accounts_cache_evicts",
                    read_cache_stats.evicts,
                    i64
                ),
                (
                    "read_only_accounts_cache_load_us",
                    read_cache_stats.load_us,
                    i64
                ),
                (
                    "read_only_accounts_cache_store_us",
                    read_cache_stats.store_us,
                    i64
                ),
                (
                    "read_only_accounts_cache_evict_us",
                    read_cache_stats.evict_us,
                    i64
                ),
                (
                    "read_only_accounts_cache_evictor_wakeup_count_all",
                    read_cache_stats.evictor_wakeup_count_all,
                    i64
                ),
                (
                    "read_only_accounts_cache_evictor_wakeup_count_productive",
                    read_cache_stats.evictor_wakeup_count_productive,
                    i64
                ),
                (
                    "handle_dead_keys_us",
                    self.stats.handle_dead_keys_us.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "purge_exact_us",
                    self.stats.purge_exact_us.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "purge_exact_count",
                    self.stats.purge_exact_count.swap(0, Ordering::Relaxed),
                    i64
                ),
            );

            datapoint_info!(
                "accounts_db_store_timings2",
                (
                    "create_store_count",
                    self.stats.create_store_count.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "store_get_slot_store",
                    self.stats.store_get_slot_store.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "store_find_existing",
                    self.stats.store_find_existing.swap(0, Ordering::Relaxed),
                    i64
                ),
                (
                    "dropped_stores",
                    self.stats.dropped_stores.swap(0, Ordering::Relaxed),
                    i64
                ),
            );
        }
    }

    /// Stores accounts in the write cache and updates the index.
    /// This should only be used for accounts that are unrooted (unfrozen)
    fn store_accounts_unfrozen<'a>(
        &self,
        accounts: impl StorableAccounts<'a>,
        transactions: Option<&'a [&'a SanitizedTransaction]>,
        update_index_thread_selection: UpdateIndexThreadSelection,
    ) {
        let slot = accounts.target_slot();

        // Store the accounts in the write cache
        let mut store_accounts_time = Measure::start("store_accounts");
        let infos = self.write_accounts_to_cache(slot, &accounts, transactions);
        store_accounts_time.stop();
        self.stats
            .store_accounts
            .fetch_add(store_accounts_time.as_us(), Ordering::Relaxed);

        // Update the index
        let mut update_index_time = Measure::start("update_index");

        self.update_index(
            infos,
            &accounts,
            UpsertReclaim::PreviousSlotEntryWasCached,
            update_index_thread_selection,
            &self.thread_pool,
        );

        update_index_time.stop();
        self.stats
            .store_update_index
            .fetch_add(update_index_time.as_us(), Ordering::Relaxed);
        self.stats
            .store_num_accounts
            .fetch_add(accounts.len() as u64, Ordering::Relaxed);
    }

    /// Stores accounts in the storage and updates the index.
    /// This should only be used on accounts that are rooted (frozen)
    pub fn store_accounts_frozen<'a>(
        &self,
        accounts: impl StorableAccounts<'a>,
        storage: &Arc<AccountStorageEntry>,
    ) -> StoreAccountsTiming {
        let slot = accounts.target_slot();
        let mut store_accounts_time = Measure::start("store_accounts");

        // Flush the read cache if neccessary. This will occur during shrink or clean
        if self.read_only_accounts_cache.can_slot_be_in_cache(slot) {
            (0..accounts.len()).for_each(|index| {
                // based on the patterns of how a validator writes accounts, it is almost always the case that there is no read only cache entry
                // for this pubkey and slot. So, we can give that hint to the `remove` for performance.
                self.read_only_accounts_cache
                    .remove_assume_not_present(accounts.pubkey(index));
            });
        }

        // Write the accounts to storage
        let infos = self.write_accounts_to_storage(slot, storage, &accounts);
        store_accounts_time.stop();
        self.stats
            .store_accounts
            .fetch_add(store_accounts_time.as_us(), Ordering::Relaxed);
        let mut update_index_time = Measure::start("update_index");

        let reclaim = UpsertReclaim::IgnoreReclaims;

        // if we are squashing a single slot, then we can expect a single dead slot
        let expected_single_dead_slot =
            (!accounts.contains_multiple_slots()).then(|| accounts.target_slot());

        // If the cache was flushed, then because `update_index` occurs
        // after the account are stored by the above `store_accounts_to`
        // call and all the accounts are stored, all reads after this point
        // will know to not check the cache anymore
        let reclaims = self.update_index(
            infos,
            &accounts,
            UpsertReclaim::IgnoreReclaims,
            UpdateIndexThreadSelection::PoolWithThreshold,
            &self.thread_pool_clean,
        );

        update_index_time.stop();
        self.stats
            .store_update_index
            .fetch_add(update_index_time.as_us(), Ordering::Relaxed);
        self.stats
            .store_num_accounts
            .fetch_add(accounts.len() as u64, Ordering::Relaxed);

        // A store for a single slot should:
        // 1) Only make "reclaims" for the same slot
        // 2) Should not cause any slots to be removed from the storage
        // database because
        //    a) this slot  has at least one account (the one being stored),
        //    b)From 1) we know no other slots are included in the "reclaims"
        //
        // From 1) and 2) we guarantee passing `no_purge_stats` == None, which is
        // equivalent to asserting there will be no dead slots, is safe.
        let mut handle_reclaims_elapsed = 0;
        if reclaim == UpsertReclaim::PopulateReclaims {
            let mut handle_reclaims_time = Measure::start("handle_reclaims");
            self.handle_reclaims(
                (!reclaims.is_empty()).then(|| reclaims.iter()),
                expected_single_dead_slot,
                &HashSet::default(),
                // this callsite does NOT process dead slots
                HandleReclaims::DoNotProcessDeadSlots,
                MarkAccountsObsolete::No,
            );
            handle_reclaims_time.stop();
            handle_reclaims_elapsed = handle_reclaims_time.as_us();
            self.stats
                .store_handle_reclaims
                .fetch_add(handle_reclaims_elapsed, Ordering::Relaxed);
        } else {
            assert!(reclaims.is_empty());
        }

        StoreAccountsTiming {
            store_accounts_elapsed: store_accounts_time.as_us(),
            update_index_elapsed: update_index_time.as_us(),
            handle_reclaims_elapsed,
        }
    }

    pub fn add_root(&self, slot: Slot) -> AccountsAddRootTiming {
        let mut index_time = Measure::start("index_add_root");
        self.accounts_index.add_root(slot);
        index_time.stop();
        let mut cache_time = Measure::start("cache_add_root");
        self.accounts_cache.add_root(slot);
        cache_time.stop();
        let mut store_time = Measure::start("store_add_root");
        // We would not expect this slot to be shrinking right now, but other slots may be.
        // But, even if it was, we would just mark a store id as dirty unnecessarily and that is ok.
        // So, allow shrinking to be in progress.
        if let Some(store) = self
            .storage
            .get_slot_storage_entry_shrinking_in_progress_ok(slot)
        {
            self.dirty_stores.insert(slot, store);
        }
        store_time.stop();

        AccountsAddRootTiming {
            index_us: index_time.as_us(),
            cache_us: cache_time.as_us(),
            store_us: store_time.as_us(),
        }
    }

    /// Returns storages for `requested_slots`
    pub fn get_storages(
        &self,
        requested_slots: impl RangeBounds<Slot> + Sync,
    ) -> (Vec<Arc<AccountStorageEntry>>, Vec<Slot>) {
        let start = Instant::now();
        let (slots, storages) = self
            .storage
            .get_if(|slot, storage| requested_slots.contains(slot) && storage.has_accounts())
            .into_vec()
            .into_iter()
            .unzip();
        let duration = start.elapsed();
        debug!("get_snapshot_storages: {duration:?}");
        (storages, slots)
    }

    /// Returns the latest full snapshot slot
    pub fn latest_full_snapshot_slot(&self) -> Option<Slot> {
        self.latest_full_snapshot_slot.read()
    }

    /// Sets the latest full snapshot slot to `slot`
    pub fn set_latest_full_snapshot_slot(&self, slot: Slot) {
        *self.latest_full_snapshot_slot.lock_write() = Some(slot);
    }

    fn generate_index_for_slot(
        &self,
        storage: &AccountStorageEntry,
        slot: Slot,
        store_id: AccountsFileId,
        storage_info: &StorageSizeAndCountMap,
    ) -> SlotIndexGenerationInfo {
        if storage.accounts.get_account_data_lens(&[0]).is_empty() {
            return SlotIndexGenerationInfo::default();
        }
        let secondary = !self.account_indexes.is_empty();

        let mut accounts_data_len = 0;
        let mut stored_size_alive = 0;
        let mut zero_lamport_pubkeys = vec![];
        let mut all_accounts_are_zero_lamports = true;

        let (insert_time_us, generate_index_results) = {
            let mut keyed_account_infos = vec![];
            // this closure is the shared code when scanning the storage
            let mut itemizer = |info: IndexInfo| {
                stored_size_alive += info.stored_size_aligned;
                if info.index_info.lamports > 0 {
                    accounts_data_len += info.index_info.data_len;
                    all_accounts_are_zero_lamports = false;
                } else {
                    // zero lamport accounts
                    zero_lamport_pubkeys.push(info.index_info.pubkey);
                }
                keyed_account_infos.push((
                    info.index_info.pubkey,
                    AccountInfo::new(
                        StorageLocation::AppendVec(store_id, info.index_info.offset), // will never be cached
                        info.index_info.is_zero_lamport(),
                    ),
                ));
            };

            if secondary {
                // WITH secondary indexes -- scan accounts WITH account data
                storage.accounts.scan_accounts(|offset, account| {
                    let data_len = account.data.len() as u64;
                    let stored_size_aligned =
                        storage.accounts.calculate_stored_size(data_len as usize);
                    let info = IndexInfo {
                        stored_size_aligned,
                        index_info: IndexInfoInner {
                            offset,
                            pubkey: *account.pubkey,
                            lamports: account.lamports,
                            data_len,
                        },
                    };
                    itemizer(info);
                    self.accounts_index.update_secondary_indexes(
                        account.pubkey,
                        &account,
                        &self.account_indexes,
                    );
                })
            } else {
                // withOUT secondary indexes -- scan accounts withOUT account data
                storage
                    .accounts
                    .scan_accounts_without_data(|offset, account| {
                        let data_len = account.data_len as u64;
                        let stored_size_aligned =
                            storage.accounts.calculate_stored_size(data_len as usize);
                        let info = IndexInfo {
                            stored_size_aligned,
                            index_info: IndexInfoInner {
                                offset,
                                pubkey: *account.pubkey,
                                lamports: account.lamports,
                                data_len,
                            },
                        };
                        itemizer(info);
                    })
            }
            .expect("must scan accounts storage");
            self.accounts_index
                .insert_new_if_missing_into_primary_index(slot, keyed_account_infos)
        };

        {
            // second, collect into the shared DashMap once we've figured out all the info per store_id
            let mut info = storage_info.entry(store_id).or_default();
            info.stored_size += stored_size_alive;
            info.count += generate_index_results.count;

            // sanity check that stored_size is not larger than the u64 aligned size of the accounts files.
            // Note that the stored_size is aligned, so it can be larger than the size of the accounts file.
            assert!(
                info.stored_size <= u64_align!(storage.accounts.len()),
                "Stored size ({}) is larger than the size of the accounts file ({}) for store_id: \
                 {}",
                info.stored_size,
                storage.accounts.len(),
                store_id
            );
        }
        // zero_lamport_pubkeys are candidates for cleaning. So add them to uncleaned_pubkeys
        // for later cleaning. If there is just a single item, there is no cleaning to
        // be done on that pubkey. Use only those pubkeys with multiple updates.
        if !zero_lamport_pubkeys.is_empty() {
            let old = self
                .uncleaned_pubkeys
                .insert(slot, zero_lamport_pubkeys.clone());
            assert!(old.is_none());
        }
        SlotIndexGenerationInfo {
            insert_time_us,
            num_accounts: generate_index_results.count as u64,
            accounts_data_len,
            zero_lamport_pubkeys,
            all_accounts_are_zero_lamports,
            num_did_not_exist: generate_index_results.num_did_not_exist,
            num_existed_in_mem: generate_index_results.num_existed_in_mem,
            num_existed_on_disk: generate_index_results.num_existed_on_disk,
        }
    }

    pub fn generate_index(
        &self,
        limit_load_slot_count_from_snapshot: Option<usize>,
        verify: bool,
        should_calculate_duplicates_lt_hash: bool,
    ) -> IndexGenerationInfo {
        let mut total_time = Measure::start("generate_index");
        let mut slots = self.storage.all_slots();
        slots.sort_unstable();
        if let Some(limit) = limit_load_slot_count_from_snapshot {
            slots.truncate(limit); // get rid of the newer slots and keep just the older
        }
        let accounts_data_len = AtomicU64::new(0);

        let zero_lamport_pubkeys = Mutex::new(HashSet::new());
        let mut outer_duplicates_lt_hash = None;

        // pass == 0 always runs and generates the index
        // pass == 1 only runs if verify == true.
        // verify checks that all the expected items are in the accounts index and measures how long it takes to look them all up
        let passes = if verify { 2 } else { 1 };
        for pass in 0..passes {
            if pass == 0 {
                self.accounts_index
                    .set_startup(Startup::StartupWithExtraThreads);
            }
            let storage_info = StorageSizeAndCountMap::default();
            let total_processed_slots_across_all_threads = AtomicU64::new(0);
            let outer_slots_len = slots.len();
            let threads = num_cpus::get();
            let chunk_size = (outer_slots_len / (std::cmp::max(1, threads.saturating_sub(1)))) + 1; // approximately 400k slots in a snapshot
            let mut index_time = Measure::start("index");
            let insertion_time_us = AtomicU64::new(0);
            let total_including_duplicates = AtomicU64::new(0);
            let all_accounts_are_zero_lamports_slots = AtomicU64::new(0);
            let mut all_zeros_slots = Mutex::new(Vec::<(Slot, Arc<AccountStorageEntry>)>::new());
            let scan_time: u64 = slots
                .par_chunks(chunk_size)
                .map(|slots| {
                    let mut log_status = MultiThreadProgress::new(
                        &total_processed_slots_across_all_threads,
                        2,
                        outer_slots_len as u64,
                    );
                    let mut scan_time_sum = 0;
                    let mut all_accounts_are_zero_lamports_slots_inner = 0;
                    let mut all_zeros_slots_inner = vec![];
                    let mut local_zero_lamport_pubkeys = Vec::new();
                    let mut insert_time_sum = 0;
                    let mut total_including_duplicates_sum = 0;
                    let mut accounts_data_len_sum = 0;
                    let mut local_num_did_not_exist = 0;
                    let mut local_num_existed_in_mem = 0;
                    let mut local_num_existed_on_disk = 0;
                    for (index, slot) in slots.iter().enumerate() {
                        let mut scan_time = Measure::start("scan");
                        log_status.report(index as u64);
                        let Some(storage) = self.storage.get_slot_storage_entry(*slot) else {
                            // no storage at this slot, no information to pull out
                            continue;
                        };
                        let store_id = storage.id();

                        scan_time.stop();
                        scan_time_sum += scan_time.as_us();

                        let insert_us = if pass == 0 {
                            // generate index
                            self.maybe_throttle_index_generation();
                            let SlotIndexGenerationInfo {
                                insert_time_us: insert_us,
                                num_accounts: total_this_slot,
                                accounts_data_len: accounts_data_len_this_slot,
                                zero_lamport_pubkeys: mut zero_lamport_pubkeys_this_slot,
                                all_accounts_are_zero_lamports,
                                num_did_not_exist,
                                num_existed_in_mem,
                                num_existed_on_disk,
                            } = self.generate_index_for_slot(
                                &storage,
                                *slot,
                                store_id,
                                &storage_info,
                            );

                            local_num_did_not_exist += num_did_not_exist;
                            local_num_existed_in_mem += num_existed_in_mem;
                            local_num_existed_on_disk += num_existed_on_disk;
                            total_including_duplicates_sum += total_this_slot;
                            accounts_data_len_sum += accounts_data_len_this_slot;
                            if all_accounts_are_zero_lamports {
                                all_accounts_are_zero_lamports_slots_inner += 1;
                                all_zeros_slots_inner.push((*slot, Arc::clone(&storage)));
                            }
                            local_zero_lamport_pubkeys.append(&mut zero_lamport_pubkeys_this_slot);

                            insert_us
                        } else {
                            // verify index matches expected and measure the time to get all items
                            assert!(verify);
                            let mut lookup_time = Measure::start("lookup_time");
                            storage
                                .accounts
                                .scan_accounts_without_data(|offset, account| {
                                    let key = account.pubkey();
                                    let index_entry = self.accounts_index.get_cloned(key).unwrap();
                                    let slot_list = index_entry.slot_list.read().unwrap();
                                    let mut count = 0;
                                    for (slot2, account_info2) in slot_list.iter() {
                                        if slot2 == slot {
                                            count += 1;
                                            let ai = AccountInfo::new(
                                                StorageLocation::AppendVec(store_id, offset), // will never be cached
                                                account.is_zero_lamport(),
                                            );
                                            assert_eq!(&ai, account_info2);
                                        }
                                    }
                                    assert_eq!(1, count);
                                })
                                .expect("must scan accounts storage");
                            lookup_time.stop();
                            lookup_time.as_us()
                        };
                        insert_time_sum += insert_us;
                    }

                    if pass == 0 {
                        let mut zero_lamport_pubkeys_lock = zero_lamport_pubkeys.lock().unwrap();
                        zero_lamport_pubkeys_lock.reserve(local_zero_lamport_pubkeys.len());
                        zero_lamport_pubkeys_lock.extend(local_zero_lamport_pubkeys.into_iter());
                        drop(zero_lamport_pubkeys_lock);

                        // This thread has finished processing its chunk of slots.
                        // Update the index stats now.
                        let index_stats = self.accounts_index.bucket_map_holder_stats();

                        // stats for inserted entries that previously did *not* exist
                        index_stats.inc_insert_count(local_num_did_not_exist);
                        index_stats.add_mem_count(local_num_did_not_exist as usize);

                        // stats for inserted entries that previous did exist *in-mem*
                        index_stats
                            .entries_from_mem
                            .fetch_add(local_num_existed_in_mem, Ordering::Relaxed);
                        index_stats
                            .updates_in_mem
                            .fetch_add(local_num_existed_in_mem, Ordering::Relaxed);

                        // stats for inserted entries that previously did exist *on-disk*
                        index_stats.add_mem_count(local_num_existed_on_disk as usize);
                        index_stats
                            .entries_missing
                            .fetch_add(local_num_existed_on_disk, Ordering::Relaxed);
                        index_stats
                            .updates_in_mem
                            .fetch_add(local_num_existed_on_disk, Ordering::Relaxed);
                    }

                    all_accounts_are_zero_lamports_slots.fetch_add(
                        all_accounts_are_zero_lamports_slots_inner,
                        Ordering::Relaxed,
                    );
                    all_zeros_slots
                        .lock()
                        .unwrap()
                        .append(&mut all_zeros_slots_inner);
                    insertion_time_us.fetch_add(insert_time_sum, Ordering::Relaxed);
                    total_including_duplicates
                        .fetch_add(total_including_duplicates_sum, Ordering::Relaxed);
                    accounts_data_len.fetch_add(accounts_data_len_sum, Ordering::Relaxed);
                    scan_time_sum
                })
                .sum();
            index_time.stop();

            let mut index_flush_us = 0;
            let total_duplicate_slot_keys = AtomicU64::default();
            let mut populate_duplicate_keys_us = 0;
            let total_num_unique_duplicate_keys = AtomicU64::default();

            // outer vec is accounts index bin (determined by pubkey value)
            // inner vec is the pubkeys within that bin that are present in > 1 slot
            let unique_pubkeys_by_bin = Mutex::new(Vec::<Vec<Pubkey>>::default());
            if pass == 0 {
                // tell accounts index we are done adding the initial accounts at startup
                let mut m = Measure::start("accounts_index_idle_us");
                self.accounts_index.set_startup(Startup::Normal);
                m.stop();
                index_flush_us = m.as_us();

                populate_duplicate_keys_us = measure_us!({
                    // this has to happen before visit_duplicate_pubkeys_during_startup below
                    // get duplicate keys from acct idx. We have to wait until we've finished flushing.
                    self.accounts_index
                        .populate_and_retrieve_duplicate_keys_from_startup(|slot_keys| {
                            total_duplicate_slot_keys
                                .fetch_add(slot_keys.len() as u64, Ordering::Relaxed);
                            let unique_keys =
                                HashSet::<Pubkey>::from_iter(slot_keys.iter().map(|(_, key)| *key));
                            for (slot, key) in slot_keys {
                                self.uncleaned_pubkeys.entry(slot).or_default().push(key);
                            }
                            let unique_pubkeys_by_bin_inner =
                                unique_keys.into_iter().collect::<Vec<_>>();
                            total_num_unique_duplicate_keys.fetch_add(
                                unique_pubkeys_by_bin_inner.len() as u64,
                                Ordering::Relaxed,
                            );
                            // does not matter that this is not ordered by slot
                            unique_pubkeys_by_bin
                                .lock()
                                .unwrap()
                                .push(unique_pubkeys_by_bin_inner);
                        });
                })
                .1;
            }
            let unique_pubkeys_by_bin = unique_pubkeys_by_bin.into_inner().unwrap();

            let mut timings = GenerateIndexTimings {
                index_flush_us,
                scan_time,
                index_time: index_time.as_us(),
                insertion_time_us: insertion_time_us.load(Ordering::Relaxed),
                total_duplicate_slot_keys: total_duplicate_slot_keys.load(Ordering::Relaxed),
                total_num_unique_duplicate_keys: total_num_unique_duplicate_keys
                    .load(Ordering::Relaxed),
                populate_duplicate_keys_us,
                total_including_duplicates: total_including_duplicates.load(Ordering::Relaxed),
                total_slots: slots.len() as u64,
                all_accounts_are_zero_lamports_slots: all_accounts_are_zero_lamports_slots
                    .load(Ordering::Relaxed),
                ..GenerateIndexTimings::default()
            };

            if pass == 0 {
                #[derive(Debug, Default)]
                struct DuplicatePubkeysVisitedInfo {
                    accounts_data_len_from_duplicates: u64,
                    num_duplicate_accounts: u64,
                    duplicates_lt_hash: Option<Box<DuplicatesLtHash>>,
                }
                impl DuplicatePubkeysVisitedInfo {
                    fn reduce(mut self, other: Self) -> Self {
                        self.accounts_data_len_from_duplicates +=
                            other.accounts_data_len_from_duplicates;
                        self.num_duplicate_accounts += other.num_duplicate_accounts;

                        match (
                            self.duplicates_lt_hash.is_some(),
                            other.duplicates_lt_hash.is_some(),
                        ) {
                            (true, true) => {
                                // SAFETY: We just checked that both values are Some
                                self.duplicates_lt_hash
                                    .as_mut()
                                    .unwrap()
                                    .0
                                    .mix_in(&other.duplicates_lt_hash.as_ref().unwrap().0);
                            }
                            (true, false) => {
                                // nothing to do; `other` doesn't have a duplicates lt hash
                            }
                            (false, true) => {
                                // `self` doesn't have a duplicates lt hash, so pilfer from `other`
                                self.duplicates_lt_hash = other.duplicates_lt_hash;
                            }
                            (false, false) => {
                                // nothing to do; no duplicates lt hash at all
                            }
                        }
                        self
                    }
                }

                let zero_lamport_pubkeys_to_visit =
                    std::mem::take(&mut *zero_lamport_pubkeys.lock().unwrap());
                let (num_zero_lamport_single_refs, visit_zero_lamports_us) =
                    measure_us!(self
                        .visit_zero_lamport_pubkeys_during_startup(&zero_lamport_pubkeys_to_visit));
                timings.visit_zero_lamports_us = visit_zero_lamports_us;
                timings.num_zero_lamport_single_refs = num_zero_lamport_single_refs;

                // subtract data.len() from accounts_data_len for all old accounts that are in the index twice
                let mut accounts_data_len_dedup_timer =
                    Measure::start("handle accounts data len duplicates");
                let DuplicatePubkeysVisitedInfo {
                    accounts_data_len_from_duplicates,
                    num_duplicate_accounts,
                    duplicates_lt_hash,
                } = unique_pubkeys_by_bin
                    .par_iter()
                    .fold(
                        DuplicatePubkeysVisitedInfo::default,
                        |accum, pubkeys_by_bin| {
                            let intermediate = pubkeys_by_bin
                                .par_chunks(4096)
                                .fold(DuplicatePubkeysVisitedInfo::default, |accum, pubkeys| {
                                    let (
                                        accounts_data_len_from_duplicates,
                                        accounts_duplicates_num,
                                        duplicates_lt_hash,
                                    ) = self.visit_duplicate_pubkeys_during_startup(
                                        pubkeys,
                                        &timings,
                                        should_calculate_duplicates_lt_hash,
                                    );
                                    let intermediate = DuplicatePubkeysVisitedInfo {
                                        accounts_data_len_from_duplicates,
                                        num_duplicate_accounts: accounts_duplicates_num,
                                        duplicates_lt_hash,
                                    };
                                    DuplicatePubkeysVisitedInfo::reduce(accum, intermediate)
                                })
                                .reduce(
                                    DuplicatePubkeysVisitedInfo::default,
                                    DuplicatePubkeysVisitedInfo::reduce,
                                );
                            DuplicatePubkeysVisitedInfo::reduce(accum, intermediate)
                        },
                    )
                    .reduce(
                        DuplicatePubkeysVisitedInfo::default,
                        DuplicatePubkeysVisitedInfo::reduce,
                    );
                accounts_data_len_dedup_timer.stop();
                timings.accounts_data_len_dedup_time_us = accounts_data_len_dedup_timer.as_us();
                timings.num_duplicate_accounts = num_duplicate_accounts;

                accounts_data_len.fetch_sub(accounts_data_len_from_duplicates, Ordering::Relaxed);
                if let Some(duplicates_lt_hash) = duplicates_lt_hash {
                    let old_val = outer_duplicates_lt_hash.replace(duplicates_lt_hash);
                    assert!(old_val.is_none());
                }
                info!(
                    "accounts data len: {}",
                    accounts_data_len.load(Ordering::Relaxed)
                );

                // insert all zero lamport account storage into the dirty stores and add them into the uncleaned roots for clean to pick up
                let all_zero_slots_to_clean = std::mem::take(all_zeros_slots.get_mut().unwrap());
                info!(
                    "insert all zero slots to clean at startup {}",
                    all_zero_slots_to_clean.len()
                );
                for (slot, storage) in all_zero_slots_to_clean {
                    self.dirty_stores.insert(slot, storage);
                }
            }

            if pass == 0 {
                // Need to add these last, otherwise older updates will be cleaned
                for root in &slots {
                    self.accounts_index.add_root(*root);
                }

                self.set_storage_count_and_alive_bytes(storage_info, &mut timings);
            }
            total_time.stop();
            timings.total_time_us = total_time.as_us();
            timings.report(self.accounts_index.get_startup_stats());
        }

        self.accounts_index.log_secondary_indexes();

        // The duplicates lt hash must be Some if should_calculate_duplicates_lt_hash is true.
        // But, if there were no duplicates, then we'd never set outer_duplicates_lt_hash to Some!
        // So do one last check here to ensure outer_duplicates_lt_hash is Some if we're supposed
        // to calculate the duplicates lt hash.
        if should_calculate_duplicates_lt_hash && outer_duplicates_lt_hash.is_none() {
            outer_duplicates_lt_hash = Some(Box::new(DuplicatesLtHash::default()));
        }

        IndexGenerationInfo {
            accounts_data_len: accounts_data_len.load(Ordering::Relaxed),
            duplicates_lt_hash: outer_duplicates_lt_hash,
        }
    }

    /// Startup processes can consume large amounts of memory while inserting accounts into the index as fast as possible.
    /// Calling this can slow down the insertion process to allow flushing to disk to keep pace.
    fn maybe_throttle_index_generation(&self) {
        // Only throttle if we are generating on-disk index. Throttling is not needed for in-mem index.
        if !self.accounts_index.is_disk_index_enabled() {
            return;
        }
        // This number is chosen to keep the initial ram usage sufficiently small
        // The process of generating the index is goverened entirely by how fast the disk index can be populated.
        // 10M accounts is sufficiently small that it will never have memory usage. It seems sufficiently large that it will provide sufficient performance.
        // Performance is measured by total time to generate the index.
        // Just estimating - 150M accounts can easily be held in memory in the accounts index on a 256G machine. 2-300M are also likely 'fine' during startup.
        // 550M was straining a 384G machine at startup.
        // This is a tunable parameter that just needs to be small enough to keep the generation threads from overwhelming RAM and oom at startup.
        const LIMIT: usize = 10_000_000;
        while self
            .accounts_index
            .get_startup_remaining_items_to_flush_estimate()
            > LIMIT
        {
            // 10 ms is long enough to allow some flushing to occur before insertion is resumed.
            // callers of this are typically run in parallel, so many threads will be sleeping at different starting intervals, waiting to resume insertion.
            sleep(Duration::from_millis(10));
        }
    }

    /// Visit zero lamport pubkeys and populate zero_lamport_single_ref info on
    /// storage.
    /// Returns the number of zero lamport single ref accounts found.
    fn visit_zero_lamport_pubkeys_during_startup(&self, pubkeys: &HashSet<Pubkey>) -> u64 {
        let mut count = 0;
        self.accounts_index.scan(
            pubkeys.iter(),
            |_pubkey, slots_refs, _entry| {
                let (slot_list, ref_count) = slots_refs.unwrap();
                if ref_count == 1 {
                    assert_eq!(slot_list.len(), 1);
                    let (slot_alive, account_info) = slot_list.first().unwrap();
                    assert!(!account_info.is_cached());
                    if account_info.is_zero_lamport() {
                        count += 1;
                        self.zero_lamport_single_ref_found(*slot_alive, account_info.offset());
                    }
                }
                AccountsIndexScanResult::OnlyKeepInMemoryIfDirty
            },
            None,
            false,
            ScanFilter::All,
        );
        count
    }

    /// Used during generate_index() to:
    /// 1. get the _duplicate_ accounts data len from the given pubkeys
    /// 2. get the slots that contained duplicate pubkeys
    /// 3. build up the duplicates lt hash
    ///
    /// Note this should only be used when ALL entries in the accounts index are roots.
    ///
    /// returns tuple of:
    /// - data len sum of all older duplicates
    /// - number of duplicate accounts
    /// - slots that contained duplicate pubkeys
    /// - lt hash of duplicates
    fn visit_duplicate_pubkeys_during_startup(
        &self,
        pubkeys: &[Pubkey],
        timings: &GenerateIndexTimings,
        should_calculate_duplicates_lt_hash: bool,
    ) -> (u64, u64, Option<Box<DuplicatesLtHash>>) {
        let mut accounts_data_len_from_duplicates = 0;
        let mut num_duplicate_accounts = 0_u64;
        let mut duplicates_lt_hash =
            should_calculate_duplicates_lt_hash.then(|| Box::new(DuplicatesLtHash::default()));
        let mut lt_hash_time = Duration::default();
        self.accounts_index.scan(
            pubkeys.iter(),
            |pubkey, slots_refs, _entry| {
                if let Some((slot_list, _ref_count)) = slots_refs {
                    if slot_list.len() > 1 {
                        // Only the account data len in the highest slot should be used, and the rest are
                        // duplicates.  So find the max slot to keep.
                        // Then sum up the remaining data len, which are the duplicates.
                        // All of the slots need to go in the 'uncleaned_slots' list. For clean to work properly,
                        // the slot where duplicate accounts are found in the index need to be in 'uncleaned_slots' list, too.
                        let max = slot_list.iter().map(|(slot, _)| slot).max().unwrap();
                        slot_list.iter().for_each(|(slot, account_info)| {
                            if slot == max {
                                // the info in 'max' is the most recent, current info for this pubkey
                                return;
                            }
                            let maybe_storage_entry = self
                                .storage
                                .get_account_storage_entry(*slot, account_info.store_id());
                            let mut accessor = LoadedAccountAccessor::Stored(
                                maybe_storage_entry.map(|entry| (entry, account_info.offset())),
                            );
                            accessor.check_and_get_loaded_account(|loaded_account| {
                                let data_len = loaded_account.data_len();
                                if loaded_account.lamports() > 0 {
                                    accounts_data_len_from_duplicates += data_len;
                                }
                                num_duplicate_accounts += 1;
                                if let Some(duplicates_lt_hash) = duplicates_lt_hash.as_mut() {
                                    let (_, duration) = meas_dur!({
                                        let account_lt_hash =
                                            Self::lt_hash_account(&loaded_account, pubkey);
                                        duplicates_lt_hash.0.mix_in(&account_lt_hash.0);
                                    });
                                    lt_hash_time += duration;
                                }
                            });
                        });
                    }
                }
                AccountsIndexScanResult::OnlyKeepInMemoryIfDirty
            },
            None,
            false,
            ScanFilter::All,
        );
        timings
            .par_duplicates_lt_hash_us
            .fetch_add(lt_hash_time.as_micros() as u64, Ordering::Relaxed);
        (
            accounts_data_len_from_duplicates as u64,
            num_duplicate_accounts,
            duplicates_lt_hash,
        )
    }

    fn set_storage_count_and_alive_bytes(
        &self,
        stored_sizes_and_counts: StorageSizeAndCountMap,
        timings: &mut GenerateIndexTimings,
    ) {
        // store count and size for each storage
        let mut storage_size_storages_time = Measure::start("storage_size_storages");
        for (_slot, store) in self.storage.iter() {
            let id = store.id();
            // Should be default at this point
            assert_eq!(store.alive_bytes(), 0);
            if let Some(entry) = stored_sizes_and_counts.get(&id) {
                trace!(
                    "id: {} setting count: {} cur: {}",
                    id,
                    entry.count,
                    store.count(),
                );
                {
                    let mut count_and_status = store.count_and_status.lock_write();
                    assert_eq!(count_and_status.0, 0);
                    count_and_status.0 = entry.count;
                }
                store
                    .alive_bytes
                    .store(entry.stored_size, Ordering::Release);
            } else {
                trace!("id: {id} clearing count");
                store.count_and_status.lock_write().0 = 0;
            }
        }
        storage_size_storages_time.stop();
        timings.storage_size_storages_us = storage_size_storages_time.as_us();
    }

    pub fn print_accounts_stats(&self, label: &str) {
        self.print_index(label);
        self.print_count_and_status(label);
    }

    fn print_index(&self, label: &str) {
        let mut alive_roots: Vec<_> = self.accounts_index.all_alive_roots();
        #[allow(clippy::stable_sort_primitive)]
        alive_roots.sort();
        info!("{label}: accounts_index alive_roots: {alive_roots:?}");
        self.accounts_index.account_maps.iter().for_each(|map| {
            for pubkey in map.keys() {
                self.accounts_index.get_and_then(&pubkey, |account_entry| {
                    if let Some(account_entry) = account_entry {
                        let list_r = &account_entry.slot_list.read().unwrap();
                        info!(" key: {} ref_count: {}", pubkey, account_entry.ref_count(),);
                        info!("      slots: {list_r:?}");
                    }
                    let add_to_in_mem_cache = false;
                    (add_to_in_mem_cache, ())
                });
            }
        });
    }

    pub fn print_count_and_status(&self, label: &str) {
        let mut slots: Vec<_> = self.storage.all_slots();
        #[allow(clippy::stable_sort_primitive)]
        slots.sort();
        info!("{}: count_and status for {} slots:", label, slots.len());
        for slot in &slots {
            let entry = self.storage.get_slot_storage_entry(*slot).unwrap();
            info!(
                "  slot: {} id: {} count_and_status: {:?} len: {} capacity: {}",
                slot,
                entry.id(),
                entry.count_and_status.read(),
                entry.accounts.len(),
                entry.accounts.capacity(),
            );
        }
    }
}

/// Should the rent_epoch field be used to compute the hash of an account?
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum RentEpochInAccountHash {
    /// Do include the rent_epoch when computing the hash of an account
    Included,
    /// Do *not* include the rent_epoch when computing the hash of an account
    Excluded,
}

/// Specify the source of the accounts data when calculating the accounts hash
///
/// Using the Index is meant for testing the hash calculation itself and debugging;
/// not intended during normal validator operation.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum CalcAccountsHashDataSource {
    IndexForTests,
    Storages,
}

#[derive(Debug, Copy, Clone)]
enum HandleReclaims<'a> {
    ProcessDeadSlots(&'a PurgeStats),
    DoNotProcessDeadSlots,
}

/// Specify whether obsolete accounts should be marked or not during reclaims
/// They should only be marked if they are also getting unreffed in the index
/// Temporariliy allow dead code until the feature is implemented
#[derive(Debug, Copy, Clone)]
enum MarkAccountsObsolete {
    #[allow(dead_code)]
    Yes(Slot),
    No,
}

/// Which accounts hash calculation is being performed?
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum CalcAccountsHashKind {
    Full,
    Incremental,
}

impl CalcAccountsHashKind {
    /// How should zero-lamport accounts be handled by this accounts hash calculation?
    fn zero_lamport_accounts(&self) -> ZeroLamportAccounts {
        match self {
            CalcAccountsHashKind::Full => ZeroLamportAccounts::Excluded,
            CalcAccountsHashKind::Incremental => ZeroLamportAccounts::Included,
        }
    }
}

pub(crate) enum UpdateIndexThreadSelection {
    /// Use current thread only
    Inline,
    /// Use a thread-pool if the number of updates exceeds a threshold
    PoolWithThreshold,
}

// These functions/fields are only usable from a dev context (i.e. tests and benches)
#[cfg(feature = "dev-context-only-utils")]
impl AccountStorageEntry {
    fn accounts_count(&self) -> usize {
        let mut count = 0;
        self.accounts
            .scan_pubkeys(|_| {
                count += 1;
            })
            .expect("must scan accounts storage");
        count
    }
}

// These functions/fields are only usable from a dev context (i.e. tests and benches)
#[cfg(feature = "dev-context-only-utils")]
impl AccountsDb {
    /// Return the number of slots marked with uncleaned pubkeys.
    /// This is useful for testing clean aglorithms.
    pub fn get_len_of_slots_with_uncleaned_pubkeys(&self) -> usize {
        self.uncleaned_pubkeys.len()
    }

    /// useful to adapt tests written prior to introduction of the write cache
    /// to use the write cache
    pub fn add_root_and_flush_write_cache(&self, slot: Slot) {
        self.add_root(slot);
        self.flush_root_write_cache(slot);
    }

    /// Wrapper function to calculate accounts delta hash for `slot` (only used for testing and benchmarking.)
    pub fn calculate_accounts_delta_hash(&self, slot: Slot) -> AccountsDeltaHash {
        self.calculate_accounts_delta_hash_internal(slot, None)
    }

    pub fn load_without_fixed_root(
        &self,
        ancestors: &Ancestors,
        pubkey: &Pubkey,
    ) -> Option<(AccountSharedData, Slot)> {
        self.do_load(
            ancestors,
            pubkey,
            None,
            LoadHint::Unspecified,
            // callers of this expect zero lamport accounts that exist in the index to be returned as Some(empty)
            LoadZeroLamports::SomeWithZeroLamportAccountForTests,
        )
    }

    pub fn accounts_delta_hashes(&self) -> &Mutex<HashMap<Slot, AccountsDeltaHash>> {
        &self.accounts_delta_hashes
    }

    pub fn accounts_hashes(&self) -> &Mutex<HashMap<Slot, (AccountsHash, /*capitalization*/ u64)>> {
        &self.accounts_hashes
    }

    pub fn assert_load_account(&self, slot: Slot, pubkey: Pubkey, expected_lamports: u64) {
        let ancestors = vec![(slot, 0)].into_iter().collect();
        let (account, slot) = self.load_without_fixed_root(&ancestors, &pubkey).unwrap();
        assert_eq!((account.lamports(), slot), (expected_lamports, slot));
    }

    pub fn assert_not_load_account(&self, slot: Slot, pubkey: Pubkey) {
        let ancestors = vec![(slot, 0)].into_iter().collect();
        let load = self.load_without_fixed_root(&ancestors, &pubkey);
        assert!(load.is_none(), "{load:?}");
    }

    pub fn check_accounts(&self, pubkeys: &[Pubkey], slot: Slot, num: usize, count: usize) {
        let ancestors = vec![(slot, 0)].into_iter().collect();
        for _ in 0..num {
            let idx = thread_rng().gen_range(0..num);
            let account = self.load_without_fixed_root(&ancestors, &pubkeys[idx]);
            let account1 = Some((
                AccountSharedData::new(
                    (idx + count) as u64,
                    0,
                    AccountSharedData::default().owner(),
                ),
                slot,
            ));
            assert_eq!(account, account1);
        }
    }

    /// callers used to call store_uncached. But, this is not allowed anymore.
    pub fn store_for_tests(&self, slot: Slot, accounts: &[(&Pubkey, &AccountSharedData)]) {
        self.store(
            (slot, accounts),
            None,
            UpdateIndexThreadSelection::PoolWithThreshold,
        );
    }

    #[allow(clippy::needless_range_loop)]
    pub fn modify_accounts(&self, pubkeys: &[Pubkey], slot: Slot, num: usize, count: usize) {
        for idx in 0..num {
            let account = AccountSharedData::new(
                (idx + count) as u64,
                0,
                AccountSharedData::default().owner(),
            );
            self.store_for_tests(slot, &[(&pubkeys[idx], &account)]);
        }
    }

    pub fn check_storage(&self, slot: Slot, alive_count: usize, total_count: usize) {
        let store = self.storage.get_slot_storage_entry(slot).unwrap();
        assert_eq!(store.status(), AccountStorageStatus::Available);
        assert_eq!(store.count(), alive_count);
        assert_eq!(store.accounts_count(), total_count);
    }

    pub fn create_account(
        &self,
        pubkeys: &mut Vec<Pubkey>,
        slot: Slot,
        num: usize,
        space: usize,
        num_vote: usize,
    ) {
        let ancestors = vec![(slot, 0)].into_iter().collect();
        for t in 0..num {
            let pubkey = solana_pubkey::new_rand();
            let account =
                AccountSharedData::new((t + 1) as u64, space, AccountSharedData::default().owner());
            pubkeys.push(pubkey);
            assert!(self.load_without_fixed_root(&ancestors, &pubkey).is_none());
            self.store_for_tests(slot, &[(&pubkey, &account)]);
        }
        for t in 0..num_vote {
            let pubkey = solana_pubkey::new_rand();
            let account =
                AccountSharedData::new((num + t + 1) as u64, space, &solana_vote_program::id());
            pubkeys.push(pubkey);
            let ancestors = vec![(slot, 0)].into_iter().collect();
            assert!(self.load_without_fixed_root(&ancestors, &pubkey).is_none());
            self.store_for_tests(slot, &[(&pubkey, &account)]);
        }
    }

    pub fn sizes_of_accounts_in_storage_for_tests(&self, slot: Slot) -> Vec<usize> {
        let mut sizes = Vec::default();
        if let Some(storage) = self.storage.get_slot_storage_entry(slot) {
            storage
                .accounts
                .scan_accounts_stored_meta(|account| {
                    sizes.push(account.stored_size());
                })
                .expect("must scan accounts storage");
        }
        sizes
    }

    pub fn ref_count_for_pubkey(&self, pubkey: &Pubkey) -> RefCount {
        self.accounts_index.ref_count_from_storage(pubkey)
    }

    pub fn alive_account_count_in_slot(&self, slot: Slot) -> usize {
        self.storage
            .get_slot_storage_entry(slot)
            .map(|storage| storage.count())
            .unwrap_or(0)
            .saturating_add(
                self.accounts_cache
                    .slot_cache(slot)
                    .map(|slot_cache| slot_cache.len())
                    .unwrap_or_default(),
            )
    }

    /// useful to adapt tests written prior to introduction of the write cache
    /// to use the write cache
    pub fn flush_root_write_cache(&self, root: Slot) {
        assert!(
            self.accounts_index
                .roots_tracker
                .read()
                .unwrap()
                .alive_roots
                .contains(&root),
            "slot: {root}"
        );
        self.flush_accounts_cache(true, Some(root));
    }

    pub fn all_account_count_in_accounts_file(&self, slot: Slot) -> usize {
        let store = self.storage.get_slot_storage_entry(slot);
        if let Some(store) = store {
            store.accounts_count()
        } else {
            0
        }
    }

    pub fn verify_accounts_hash_and_lamports_for_tests(
        &self,
        slot: Slot,
        total_lamports: u64,
        config: VerifyAccountsHashAndLamportsConfig,
    ) -> Result<(), AccountsHashVerificationError> {
        let snapshot_storages = self.get_storages(..);
        let snapshot_storages_and_slots = (
            snapshot_storages.0.as_slice(),
            snapshot_storages.1.as_slice(),
        );
        self.verify_accounts_hash_and_lamports(
            snapshot_storages_and_slots,
            slot,
            total_lamports,
            None,
            config,
        )
    }

    pub fn uncleaned_pubkeys(&self) -> &DashMap<Slot, Vec<Pubkey>, BuildNoHashHasher<Slot>> {
        &self.uncleaned_pubkeys
    }
}

// These functions/fields are only usable from a dev context (i.e. tests and benches)
#[cfg(feature = "dev-context-only-utils")]
impl<'a> VerifyAccountsHashAndLamportsConfig<'a> {
    pub fn new_for_test(
        ancestors: &'a Ancestors,
        epoch_schedule: &'a EpochSchedule,
        epoch: Epoch,
    ) -> Self {
        Self {
            ancestors,
            epoch_schedule,
            epoch,
            ignore_mismatch: false,
            store_detailed_debug_info: false,
            use_bg_thread_pool: false,
        }
    }
}

/// A set of utility functions used for testing and benchmarking
#[cfg(feature = "dev-context-only-utils")]
pub mod test_utils {
    use {super::*, crate::accounts::Accounts};

    pub fn create_test_accounts(
        accounts: &Accounts,
        pubkeys: &mut Vec<Pubkey>,
        num: usize,
        slot: Slot,
    ) {
        let data_size = 0;

        for t in 0..num {
            let pubkey = solana_pubkey::new_rand();
            let account = AccountSharedData::new(
                (t + 1) as u64,
                data_size,
                AccountSharedData::default().owner(),
            );
            accounts.store_cached((slot, &[(&pubkey, &account)][..]), None);
            pubkeys.push(pubkey);
        }
    }

    // Only used by bench, not safe to call otherwise accounts can conflict with the
    // accounts cache!
    pub fn update_accounts_bench(accounts: &Accounts, pubkeys: &[Pubkey], slot: u64) {
        for pubkey in pubkeys {
            let amount = thread_rng().gen_range(0..10);
            let account = AccountSharedData::new(amount, 0, AccountSharedData::default().owner());
            accounts.store_cached((slot, &[(pubkey, &account)][..]), None);
        }
    }
}
