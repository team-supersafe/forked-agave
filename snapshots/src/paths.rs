use {
    crate::{error::SnapshotError, snapshot_hash::SnapshotHash, ArchiveFormat, Result},
    regex::Regex,
    solana_clock::Slot,
    solana_hash::Hash,
    std::{
        path::{Path, PathBuf},
        sync::LazyLock,
    },
};

pub const SNAPSHOT_STATUS_CACHE_FILENAME: &str = "status_cache";
pub const SNAPSHOT_VERSION_FILENAME: &str = "version";
pub const SNAPSHOT_FASTBOOT_VERSION_FILENAME: &str = "fastboot_version";
/// No longer checked in version v3.1. Can be removed in v3.2
pub const SNAPSHOT_STATE_COMPLETE_FILENAME: &str = "state_complete";
pub const SNAPSHOT_STORAGES_FLUSHED_FILENAME: &str = "storages_flushed";
pub const SNAPSHOT_ACCOUNTS_HARDLINKS: &str = "accounts_hardlinks";
pub const SNAPSHOT_ARCHIVE_DOWNLOAD_DIR: &str = "remote";
pub const SNAPSHOT_OBSOLETE_ACCOUNTS_FILENAME: &str = "obsolete_accounts";
/// No longer checked in version v3.1. Can be removed in v3.2
pub const SNAPSHOT_FULL_SNAPSHOT_SLOT_FILENAME: &str = "full_snapshot_slot";
/// When a snapshot is taken of a bank, the state is serialized under this directory.
/// Specifically in `BANK_SNAPSHOTS_DIR/SLOT/`.
/// This is also where the bank state is located in the snapshot archive.
pub const BANK_SNAPSHOTS_DIR: &str = "snapshots";
pub const TMP_SNAPSHOT_ARCHIVE_PREFIX: &str = "tmp-snapshot-archive-";
pub const FULL_SNAPSHOT_ARCHIVE_FILENAME_REGEX: &str =
    r"^snapshot-(?P<slot>[[:digit:]]+)-(?P<hash>[[:alnum:]]+)\.(?P<ext>tar\.zst|tar\.lz4)$";
pub const INCREMENTAL_SNAPSHOT_ARCHIVE_FILENAME_REGEX: &str = r"^incremental-snapshot-(?P<base>[[:digit:]]+)-(?P<slot>[[:digit:]]+)-(?P<hash>[[:alnum:]]+)\.(?P<ext>tar\.zst|tar\.lz4)$";

/// Get the `&str` from a `&Path`
pub fn path_to_file_name_str(path: &Path) -> Result<&str> {
    path.file_name()
        .ok_or_else(|| SnapshotError::PathToFileNameError(path.to_path_buf()))?
        .to_str()
        .ok_or_else(|| SnapshotError::FileNameToStrError(path.to_path_buf()))
}

pub fn build_snapshot_archives_remote_dir(snapshot_archives_dir: impl AsRef<Path>) -> PathBuf {
    snapshot_archives_dir
        .as_ref()
        .join(SNAPSHOT_ARCHIVE_DOWNLOAD_DIR)
}

/// Build the full snapshot archive path from its components: the snapshot archives directory, the
/// snapshot slot, the accounts hash, and the archive format.
pub fn build_full_snapshot_archive_path(
    full_snapshot_archives_dir: impl AsRef<Path>,
    slot: Slot,
    hash: &SnapshotHash,
    archive_format: ArchiveFormat,
) -> PathBuf {
    full_snapshot_archives_dir.as_ref().join(format!(
        "snapshot-{}-{}.{}",
        slot,
        hash.0,
        archive_format.extension(),
    ))
}

/// Build the incremental snapshot archive path from its components: the snapshot archives
/// directory, the snapshot base slot, the snapshot slot, the accounts hash, and the archive
/// format.
pub fn build_incremental_snapshot_archive_path(
    incremental_snapshot_archives_dir: impl AsRef<Path>,
    base_slot: Slot,
    slot: Slot,
    hash: &SnapshotHash,
    archive_format: ArchiveFormat,
) -> PathBuf {
    incremental_snapshot_archives_dir.as_ref().join(format!(
        "incremental-snapshot-{}-{}-{}.{}",
        base_slot,
        slot,
        hash.0,
        archive_format.extension(),
    ))
}

/// Parse a full snapshot archive filename into its Slot, Hash, and Archive Format
pub fn parse_full_snapshot_archive_filename(
    archive_filename: &str,
) -> Result<(Slot, SnapshotHash, ArchiveFormat)> {
    static RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(FULL_SNAPSHOT_ARCHIVE_FILENAME_REGEX).unwrap());

    let do_parse = || {
        RE.captures(archive_filename).and_then(|captures| {
            let slot = captures
                .name("slot")
                .map(|x| x.as_str().parse::<Slot>())?
                .ok()?;
            let hash = captures
                .name("hash")
                .map(|x| x.as_str().parse::<Hash>())?
                .ok()?;
            let archive_format = captures
                .name("ext")
                .map(|x| x.as_str().parse::<ArchiveFormat>())?
                .ok()?;

            Some((slot, SnapshotHash(hash), archive_format))
        })
    };

    do_parse().ok_or_else(|| {
        SnapshotError::ParseSnapshotArchiveFileNameError(archive_filename.to_string())
    })
}

/// Parse an incremental snapshot archive filename into its base Slot, actual Slot, Hash, and Archive Format
pub fn parse_incremental_snapshot_archive_filename(
    archive_filename: &str,
) -> Result<(Slot, Slot, SnapshotHash, ArchiveFormat)> {
    static RE: LazyLock<Regex> =
        LazyLock::new(|| Regex::new(INCREMENTAL_SNAPSHOT_ARCHIVE_FILENAME_REGEX).unwrap());

    let do_parse = || {
        RE.captures(archive_filename).and_then(|captures| {
            let base_slot = captures
                .name("base")
                .map(|x| x.as_str().parse::<Slot>())?
                .ok()?;
            let slot = captures
                .name("slot")
                .map(|x| x.as_str().parse::<Slot>())?
                .ok()?;
            let hash = captures
                .name("hash")
                .map(|x| x.as_str().parse::<Hash>())?
                .ok()?;
            let archive_format = captures
                .name("ext")
                .map(|x| x.as_str().parse::<ArchiveFormat>())?
                .ok()?;

            Some((base_slot, slot, SnapshotHash(hash), archive_format))
        })
    };

    do_parse().ok_or_else(|| {
        SnapshotError::ParseSnapshotArchiveFileNameError(archive_filename.to_string())
    })
}

/// Returns the file name of the bank snapshot for `slot`
pub fn get_snapshot_file_name(slot: Slot) -> String {
    slot.to_string()
}

/// Constructs the path to the bank snapshot directory for `slot` within `bank_snapshots_dir`
pub fn get_bank_snapshot_dir(bank_snapshots_dir: impl AsRef<Path>, slot: Slot) -> PathBuf {
    bank_snapshots_dir
        .as_ref()
        .join(get_snapshot_file_name(slot))
}

#[cfg(test)]
mod tests {
    use {super::*, crate::ZstdConfig};

    #[test]
    fn test_parse_full_snapshot_archive_filename() {
        assert_eq!(
            parse_full_snapshot_archive_filename(&format!(
                "snapshot-43-{}.tar.zst",
                Hash::default()
            ))
            .unwrap(),
            (
                43,
                SnapshotHash(Hash::default()),
                ArchiveFormat::TarZstd {
                    config: ZstdConfig::default(),
                }
            )
        );
        assert_eq!(
            parse_full_snapshot_archive_filename(&format!(
                "snapshot-45-{}.tar.lz4",
                Hash::default()
            ))
            .unwrap(),
            (45, SnapshotHash(Hash::default()), ArchiveFormat::TarLz4)
        );

        assert!(parse_full_snapshot_archive_filename("invalid").is_err());
        assert!(
            parse_full_snapshot_archive_filename("snapshot-bad!slot-bad!hash.bad!ext").is_err()
        );

        assert!(
            parse_full_snapshot_archive_filename("snapshot-12345678-bad!hash.bad!ext").is_err()
        );
        assert!(parse_full_snapshot_archive_filename(&format!(
            "snapshot-12345678-{}.bad!ext",
            Hash::new_unique()
        ))
        .is_err());
        assert!(
            parse_full_snapshot_archive_filename("snapshot-12345678-bad!hash.tar.zst").is_err()
        );

        assert!(parse_full_snapshot_archive_filename(&format!(
            "snapshot-bad!slot-{}.bad!ext",
            Hash::new_unique()
        ))
        .is_err());
        assert!(parse_full_snapshot_archive_filename(&format!(
            "snapshot-12345678-{}.bad!ext",
            Hash::new_unique()
        ))
        .is_err());
        assert!(parse_full_snapshot_archive_filename(&format!(
            "snapshot-bad!slot-{}.tar.zst",
            Hash::new_unique()
        ))
        .is_err());

        assert!(
            parse_full_snapshot_archive_filename("snapshot-bad!slot-bad!hash.tar.zst").is_err()
        );
        assert!(
            parse_full_snapshot_archive_filename("snapshot-12345678-bad!hash.tar.zst").is_err()
        );
        assert!(parse_full_snapshot_archive_filename(&format!(
            "snapshot-bad!slot-{}.tar.zst",
            Hash::new_unique()
        ))
        .is_err());
    }

    #[test]
    fn test_parse_incremental_snapshot_archive_filename() {
        assert_eq!(
            parse_incremental_snapshot_archive_filename(&format!(
                "incremental-snapshot-43-234-{}.tar.zst",
                Hash::default()
            ))
            .unwrap(),
            (
                43,
                234,
                SnapshotHash(Hash::default()),
                ArchiveFormat::TarZstd {
                    config: ZstdConfig::default(),
                }
            )
        );
        assert_eq!(
            parse_incremental_snapshot_archive_filename(&format!(
                "incremental-snapshot-45-456-{}.tar.lz4",
                Hash::default()
            ))
            .unwrap(),
            (
                45,
                456,
                SnapshotHash(Hash::default()),
                ArchiveFormat::TarLz4
            )
        );

        assert!(parse_incremental_snapshot_archive_filename("invalid").is_err());
        assert!(parse_incremental_snapshot_archive_filename(&format!(
            "snapshot-42-{}.tar.zst",
            Hash::new_unique()
        ))
        .is_err());
        assert!(parse_incremental_snapshot_archive_filename(
            "incremental-snapshot-bad!slot-bad!slot-bad!hash.bad!ext"
        )
        .is_err());

        assert!(parse_incremental_snapshot_archive_filename(&format!(
            "incremental-snapshot-bad!slot-56785678-{}.tar.zst",
            Hash::new_unique()
        ))
        .is_err());

        assert!(parse_incremental_snapshot_archive_filename(&format!(
            "incremental-snapshot-12345678-bad!slot-{}.tar.zst",
            Hash::new_unique()
        ))
        .is_err());

        assert!(parse_incremental_snapshot_archive_filename(
            "incremental-snapshot-12341234-56785678-bad!HASH.tar.zst"
        )
        .is_err());

        assert!(parse_incremental_snapshot_archive_filename(&format!(
            "incremental-snapshot-12341234-56785678-{}.bad!ext",
            Hash::new_unique()
        ))
        .is_err());
    }
}
