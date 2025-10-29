#![cfg_attr(
    not(feature = "agave-unstable-api"),
    deprecated(
        since = "3.1.0",
        note = "This crate has been marked for formal inclusion in the Agave Unstable API. From \
                v4.0.0 onward, the `agave-unstable-api` crate feature must be specified to \
                acknowledge use of an interface that may break without warning."
    )
)]
#![no_std]

//! Messages passed between agave and an external pack process.
//! Messages are passed via `shaq::Consumer/Producer`.
//!
//! Memory freeing is responsibility of the external pack process,
//! and is done via `rts-alloc` crate. It is also possible the external
//! pack process allocates memory to pass to agave, BUT it will still be
//! the responsibility of the external pack process to free that memory.
//!
//! Setting up the shared memory allocator and queues is done outside of
//! agave - it can be done by the external pack process or another
//! process. agave will just `join` shared memory regions, but not
//! create them.
//! Similarly, agave will not delete files used for shared memory regions.
//! See `shaq` and `rts-alloc` crates for details.
//!
//! The basic architecture is as follows:
//!        ┌───────────────┐       ┌─────────────────┐
//!        │  tpu_to_pack  │       │ progress_tracker│
//!        └───────┬───────┘       └───────┬─────────┘
//!                │                       │
//!                │                       │
//!                │                       │
//!             ┌──▼───────────────────────▼───┐
//!             │  external scheduler          │
//!             └─▲─────── ▲────────────────▲──┘
//!               │        │                │
//!               │        │                │
//!           ┌───▼───┐ ┌──▼─────┐ ...  ┌───▼───┐
//!           │worker1│ │worker2 │      │workerN│
//!           └───────┘ └────────┘      └───────┘
//!
//! - [`TpuToPackMessage`] are sent from `tpu_to_pack` queue to the
//!   external scheduler process. This passes in tpu transactions to be scheduled,
//!   and optionally vote transactions.
//! - [`ProgressMessage`] are sent from `progress_tracker` queue to the
//!   external scheduler process. This passes information about leader status
//!   and slot progress to the external scheduler process.
//! - [`PackToWorkerMessage`] are sent from the external scheduler process
//!   to worker threads within agave. This passes a batch of transactions
//!   to be processed by the worker threads. This processing can also involve
//!   resolving the transactions' addresses, or similar operations beyond
//!   execution.
//! - [`WorkerToPackMessage`] are sent from worker threads within agave
//!   back to the external scheduler process. This passes back the results
//!   of processing the transactions.
//!

/// Reference to a transaction that can shared safely across processes.
#[cfg_attr(
    feature = "dev-context-only-utils",
    derive(Debug, Clone, Copy, PartialEq, Eq)
)]
#[repr(C)]
pub struct SharableTransactionRegion {
    /// Offset within the shared memory allocator.
    pub offset: usize,
    /// Length of the transaction in bytes.
    pub length: u32,
}

/// Reference to an array of Pubkeys that can be shared safely across processes.
#[cfg_attr(
    feature = "dev-context-only-utils",
    derive(Debug, Clone, Copy, PartialEq, Eq)
)]
#[repr(C)]
pub struct SharablePubkeys {
    /// Offset within the shared memory allocator.
    pub offset: usize,
    /// Number of pubkeys in the array.
    /// IF 0, indicates no pubkeys and no allocation needing to be freed.
    pub num_pubkeys: u32,
}

/// Reference to an array of [`SharableTransactionRegion`] that can be shared safely
/// across processes.
/// General flow:
/// 1. External pack process allocates memory for
///    `num_transactions` [`SharableTransactionRegion`].
/// 2. External pack sends a [`PackToWorkerMessage`] with `batch`.
/// 3. agave processes the transactions and sends back a [`WorkerToPackMessage`]
///    with the same `batch`.
/// 4. External pack process frees all transaction memory pointed to by the
///    [`SharableTransactionRegion`] in the batch, then frees the memory for
///    the array of [`SharableTransactionRegion`].
#[cfg_attr(feature = "dev-context-only-utils", derive(Debug, PartialEq, Eq))]
#[derive(Clone, Copy)]
#[repr(C)]
pub struct SharableTransactionBatchRegion {
    /// Number of transactions in the batch.
    pub num_transactions: u8,
    /// Offset within the shared memory allocator for the batch of transactions.
    /// The transactions are laid out back-to-back in memory as a
    /// [`SharableTransactionRegion`] with size `num_transactions`.
    pub transactions_offset: usize,
}
/// Reference to an array of response messages.
/// General flow:
/// 1. agave allocates memory for `num_transaction_responses` inner messages.
/// 2. agave sends a [`WorkerToPackMessage`] with `responses`.
/// 3. External pack process processes the inner messages. Potentially freeing
///    any memory within each inner message (see [`worker_message_types`] for details).
#[cfg_attr(
    feature = "dev-context-only-utils",
    derive(Debug, Clone, Copy, PartialEq, Eq)
)]
#[repr(C)]
pub struct TransactionResponseRegion {
    /// Tag indicating the type of message.
    /// See [`worker_message_types`] for details.
    /// All inner messages/responses per trasaction will be of the same type.
    pub tag: u8,
    /// The number of transactions in the original message.
    /// This corresponds to the number of inner response
    /// messages that will be pointed to by `response_offset`.
    /// This MUST be the same as `batch.num_transactions`.
    pub num_transaction_responses: u8,
    /// Offset within the shared memory allocator for the array of
    /// inner messages.
    /// The inner messages are laid out back-to-back in memory starting at
    /// this offset. The type of each inner message is indicated by `tag`.
    /// There are `num_transaction_responses` inner messages.
    /// See [`worker_message_types`] for details on the inner message types.
    pub transaction_responses_offset: usize,
}

/// Message: [TPU -> Pack]
/// TPU passes transactions to the external pack process.
/// This is also a transfer of ownership of the transaction:
///   the external pack process is responsible for freeing the memory.
#[cfg_attr(
    feature = "dev-context-only-utils",
    derive(Debug, Clone, Copy, PartialEq, Eq)
)]
#[repr(C)]
pub struct TpuToPackMessage {
    pub transaction: SharableTransactionRegion,
    /// See [`tpu_message_flags`] for details.
    pub flags: u8,
    /// The source address of the transaction.
    /// IPv6-mapped IPv4 addresses: `::ffff:a.b.c.d`
    /// where a.b.c.d is the IPv4 address.
    /// See <https://datatracker.ietf.org/doc/html/rfc4291#section-2.5.5.2>.
    pub src_addr: [u8; 16],
}

pub mod tpu_message_flags {
    /// No special flags.
    pub const NONE: u8 = 0;

    /// The transaction is a simple vote transaction.
    pub const IS_SIMPLE_VOTE: u8 = 1 << 0;
    /// The transaction was forwarded by a validator node.
    pub const FORWARDED: u8 = 1 << 1;
    /// The transaction was sent from a staked node.
    pub const FROM_STAKED_NODE: u8 = 1 << 2;
}

/// Message: [Agave -> Pack]
/// Agave passes leader status to the external pack process.
#[cfg_attr(
    feature = "dev-context-only-utils",
    derive(Debug, Clone, Copy, PartialEq, Eq)
)]
#[repr(C)]
pub struct ProgressMessage {
    /// The current slot.
    pub current_slot: u64,
    /// Next known leader slot or u64::MAX if unknown.
    /// If currently leader, this is equal to `current_slot`.
    pub next_leader_slot: u64,
    /// The remaining cost units allowed to be packed in the block.
    /// i.e. block_limit - current_cost_units_used.
    /// Only valid if currently leader, otherwise the value is undefined.
    pub remaining_cost_units: u64,
    /// Progress through the current slot in percentage.
    pub current_slot_progress: u8,
}

/// Maximum number of transactions allowed in a [`PackToWorkerMessage`].
/// If the number of transactions exceeds this value, agave will
/// not process the message.
//
// The reason for this constraint is because rts-alloc currently only
// supports up to 4096 byte allocations. We must ensure that the
// `TransactionResponseRegion` is able to contain responses for all
// transactions sent. This is a conservative bound.
pub const MAX_TRANSACTIONS_PER_MESSAGE: usize = 64;

/// Message: [Pack -> Worker]
/// External pack processe passes transactions to worker threads within agave.
///
/// These messages do not transfer ownership of the transactions.
/// The external pack process is still responsible for freeing the memory.
#[cfg_attr(
    feature = "dev-context-only-utils",
    derive(Debug, Clone, Copy, PartialEq, Eq)
)]
#[repr(C)]
pub struct PackToWorkerMessage {
    /// Flags on how to handle this message.
    /// See [`pack_message_flags`] for details.
    pub flags: u16,
    /// If [`pack_message_flags::RESOLVE`] flag is not set, this is the
    /// maximum slot the transactions can be processed in. If the working
    /// bank's slot in the worker thread is greater than this slot,
    /// the transaction will not be processed.
    pub max_execution_slot: u64,
    /// Offset and number of transactions in the batch.
    /// See [`SharableTransactionBatchRegion`] for details.
    /// Agave will return this batch in the response message, it is
    /// the responsibility of the external pack process to free the memory
    /// ONLY after receiving the response message.
    pub batch: SharableTransactionBatchRegion,
}

pub mod pack_message_flags {
    //! Flags for [`crate::PackToWorkerMessage::flags`].
    //! These flags can be ORed together so must be unique bits, with
    //! the exception of [`NONE`].
    //! The *default* behavior, [`NONE`], is to attempt execution and
    //! inclusion in the specified `max_execution_slot`.

    /// No special handling - execute the transactions normally.
    pub const NONE: u16 = 0;

    /// Transactions on the [`super::PackToWorkerMessage`] should have their
    /// addresses resolved.
    ///
    /// If this flag, the transaction will attempt to be executed and included
    /// in the current block.
    pub const RESOLVE: u16 = 1 << 1;
}

/// Message: [Worker -> Pack]
/// Message from worker threads in response to a [`PackToWorkerMessage`].
#[cfg_attr(
    feature = "dev-context-only-utils",
    derive(Debug, Clone, Copy, PartialEq, Eq)
)]
#[repr(C)]
pub struct WorkerToPackMessage {
    /// Offset and number of transactions in the batch.
    /// See [`SharableTransactionBatchRegion`] for details.
    /// Once the external pack process receives this message,
    /// it is responsible for freeing the memory for this batch,
    /// and is safe to do so - agave will hold no references to this memory
    /// after sending this message.
    pub batch: SharableTransactionBatchRegion,
    /// `1` if the message was processed.
    /// `0` if the message could not be processed. This will occur
    /// if the passed message was invalid, and could indicate an issue
    /// with the external pack process.
    /// If `0`, the value of [`Self::responses`] is undefined.
    /// Other values should be considered invalid.
    pub processed: u8,
    /// Response per transaction in the batch.
    /// If [`Self::processed`] is false, this field is undefined.
    /// See [`TransactionResponseRegion`] for details.
    pub responses: TransactionResponseRegion,
}

pub mod worker_message_types {
    use crate::SharablePubkeys;

    /// Tag indicating [`ExecutionResponse`] inner message.
    pub const EXECUTION_RESPONSE: u8 = 0;

    /// Response to pack for a transaction that attempted execution.
    /// This response will only be sent if the original message flags
    /// requested execution i.e. not [`super::pack_message_flags::RESOLVE`].
    #[cfg_attr(
        feature = "dev-context-only-utils",
        derive(Debug, Clone, Copy, PartialEq, Eq)
    )]
    #[repr(C)]
    pub struct ExecutionResponse {
        /// Indicates if the transaction was included in the block or not.
        /// If [`not_included_reasons::NONE`], the transaction was included.
        pub not_included_reason: u8,
        /// If included, cost units used by the transaction.
        pub cost_units: u64,
        /// If included, the fee-payer balance after execution.
        pub fee_payer_balance: u64,
    }

    pub mod not_included_reasons {
        /// The transaction was included in the block.
        pub const NONE: u8 = 0;
        /// The transaction could not attempt processing because the
        /// working bank was unavailable.
        pub const BANK_NOT_AVAILABLE: u8 = 1;
        /// The transaction could not be processed because the `slot`
        /// in the passed message did not match the working bank's slot.
        pub const SLOT_MISMATCH: u8 = 2;

        /// Transaction dropped because the batch was marked as
        /// all_or_nothing and a different transacation failed.
        pub const ALL_OR_NOTHING_BATCH_FAILURE: u8 = 3;

        // Remaining errors are translations from SDK.
        // Moved up to 64 so we have room to add custom reasons in the future.
        // Also allows for easy distinguishing between custom scheduling errors
        // and sdk errors.

        /// An account is already being processed in another transaction in a way
        /// that does not support parallelism
        pub const ACCOUNT_IN_USE: u8 = 64;
        /// A `Pubkey` appears twice in the transaction's `account_keys`.  Instructions can reference
        /// `Pubkey`s more than once but the message must contain a list with no duplicate keys
        pub const ACCOUNT_LOADED_TWICE: u8 = 65;
        /// Attempt to debit an account but found no record of a prior credit.
        pub const ACCOUNT_NOT_FOUND: u8 = 66;
        /// Attempt to load a program that does not exist
        pub const PROGRAM_ACCOUNT_NOT_FOUND: u8 = 67;
        /// The from `Pubkey` does not have sufficient balance to pay the fee to schedule the transaction
        pub const INSUFFICIENT_FUNDS_FOR_FEE: u8 = 68;
        /// This account may not be used to pay transaction fees
        pub const INVALID_ACCOUNT_FOR_FEE: u8 = 69;
        /// The bank has seen this transaction before. This can occur under normal operation
        pub const ALREADY_PROCESSED: u8 = 70;
        /// The bank has not seen the given `recent_blockhash`
        pub const BLOCKHASH_NOT_FOUND: u8 = 71;
        /// An error occurred while processing an instruction.
        pub const INSTRUCTION_ERROR: u8 = 72;
        /// Loader call chain is too deep
        pub const CALL_CHAIN_TOO_DEEP: u8 = 73;
        /// Transaction requires a fee but has no signature present
        pub const MISSING_SIGNATURE_FOR_FEE: u8 = 74;
        /// Transaction contains an invalid account reference
        pub const INVALID_ACCOUNT_INDEX: u8 = 75;
        /// Transaction did not pass signature verification
        pub const SIGNATURE_FAILURE: u8 = 76;
        /// This program may not be used for executing instructions
        pub const INVALID_PROGRAM_FOR_EXECUTION: u8 = 77;
        /// Transaction failed to sanitize accounts offsets correctly
        pub const SANITIZE_FAILURE: u8 = 78;
        pub const CLUSTER_MAINTENANCE: u8 = 79;
        /// Transaction processing left an account with an outstanding borrowed reference
        pub const ACCOUNT_BORROW_OUTSTANDING: u8 = 80;
        /// Transaction would exceed max Block Cost Limit
        pub const WOULD_EXCEED_MAX_BLOCK_COST_LIMIT: u8 = 81;
        /// Transaction version is unsupported
        pub const UNSUPPORTED_VERSION: u8 = 82;
        /// Transaction loads a writable account that cannot be written
        pub const INVALID_WRITABLE_ACCOUNT: u8 = 83;
        /// Transaction would exceed max account limit within the block
        pub const WOULD_EXCEED_MAX_ACCOUNT_COST_LIMIT: u8 = 84;
        /// Transaction would exceed account data limit within the block
        pub const WOULD_EXCEED_ACCOUNT_DATA_BLOCK_LIMIT: u8 = 85;
        /// Transaction locked too many accounts
        pub const TOO_MANY_ACCOUNT_LOCKS: u8 = 86;
        /// Address lookup table not found
        pub const ADDRESS_LOOKUP_TABLE_NOT_FOUND: u8 = 87;
        /// Attempted to lookup addresses from an account owned by the wrong program
        pub const INVALID_ADDRESS_LOOKUP_TABLE_OWNER: u8 = 88;
        /// Attempted to lookup addresses from an invalid account
        pub const INVALID_ADDRESS_LOOKUP_TABLE_DATA: u8 = 89;
        /// Address table lookup uses an invalid index
        pub const INVALID_ADDRESS_LOOKUP_TABLE_INDEX: u8 = 90;
        /// Transaction leaves an account with a lower balance than rent-exempt minimum
        pub const INVALID_RENT_PAYING_ACCOUNT: u8 = 91;
        /// Transaction would exceed max Vote Cost Limit
        pub const WOULD_EXCEED_MAX_VOTE_COST_LIMIT: u8 = 92;
        /// Transaction would exceed total account data limit
        pub const WOULD_EXCEED_ACCOUNT_DATA_TOTAL_LIMIT: u8 = 93;
        /// Transaction contains a duplicate instruction that is not allowed
        pub const DUPLICATE_INSTRUCTION: u8 = 94;
        /// Transaction results in an account with insufficient funds for rent
        pub const INSUFFICIENT_FUNDS_FOR_RENT: u8 = 95;
        /// Transaction exceeded max loaded accounts data size cap
        pub const MAX_LOADED_ACCOUNTS_DATA_SIZE_EXCEEDED: u8 = 96;
        /// LoadedAccountsDataSizeLimit set for transaction must be greater than 0.
        pub const INVALID_LOADED_ACCOUNTS_DATA_SIZE_LIMIT: u8 = 97;
        /// Sanitized transaction differed before/after feature activation. Needs to be resanitized.
        pub const RESANITIZATION_NEEDED: u8 = 98;
        /// Program execution is temporarily restricted on an account.
        pub const PROGRAM_EXECUTION_TEMPORARILY_RESTRICTED: u8 = 99;
        /// The total balance before the transaction does not equal the total balance after the transaction
        pub const UNBALANCED_TRANSACTION: u8 = 100;
        /// Program cache hit max limit.
        pub const PROGRAM_CACHE_HIT_MAX_LIMIT: u8 = 101;

        // This error in agave is only internal, and to avoid updating the sdk
        // it is re-used for mapping into `ALL_OR_NOTHING_BATCH_FAILURE`.
        // /// Commit cancelled internally.
        // pub const COMMIT_CANCELLED: u8 = 102;
    }

    /// Tag indicating [`Resolved`] inner message.
    pub const RESOLVED: u8 = 1;

    #[cfg_attr(
        feature = "dev-context-only-utils",
        derive(Debug, Clone, Copy, PartialEq, Eq)
    )]
    #[repr(C)]
    pub struct Resolved {
        /// Indicates if resolution was successful.
        /// 0 = false, 1 = true.
        /// Other values should be considered invalid.
        pub success: u8,
        /// Slot of the bank used for resolution.
        pub slot: u64,
        /// Minimum deactivation slot of any ALT if any.
        /// u64::MAX if no ALTs or deactivation.
        pub min_alt_deactivation_slot: u64,
        /// Resolved pubkeys - writable then readonly.
        /// Freeing this memory is the responsiblity of the external
        /// pack process.
        pub resolved_pubkeys: SharablePubkeys,
    }
}
