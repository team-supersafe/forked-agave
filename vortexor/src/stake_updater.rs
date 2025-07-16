//! Module responsible for updating the staked key map.
//! Adapted from jito-relayer code.

use {
    crate::rpc_load_balancer::RpcLoadBalancer,
    log::{info, warn},
    solana_client::client_error,
    solana_pubkey::Pubkey,
    solana_streamer::streamer::StakedNodes,
    std::{
        collections::HashMap,
        str::FromStr,
        sync::{
            atomic::{AtomicBool, Ordering},
            Arc, RwLock,
        },
        thread::{self, sleep, Builder, JoinHandle},
        time::{Duration, Instant},
    },
};

// The interval to refresh the stake information.
// The stakes are updated at the validator every epoch, there is no need to
// refresh it via RPC too frequently.
const STAKE_REFRESH_INTERVAL: Duration = Duration::from_secs(1800);

// The interval to to sleep to check for exit condition and/or refresh condition.
pub const STAKE_REFRESH_SLEEP_DURATION: Duration = Duration::from_secs(5);

/// This service is responsible for periodically refresh the stake information
/// from the network with the assistance of the RpcLoaderBalancer.
pub struct StakeUpdater {
    thread_hdl: JoinHandle<()>,
}

impl StakeUpdater {
    pub fn new(
        exit: Arc<AtomicBool>,
        rpc_load_balancer: Arc<RpcLoadBalancer>,
        shared_staked_nodes: Arc<RwLock<StakedNodes>>,
        refresh_sleep_duration: Duration,
    ) -> Self {
        info!("Starting stake updater thread");
        let thread_hdl = Builder::new()
            .name("stkUpdtr".to_string())
            .spawn(move || {
                let mut last_stakes = None;
                while !exit.load(Ordering::Relaxed) {
                    if let Err(err) = Self::try_refresh_stake_info(
                        &mut last_stakes,
                        &shared_staked_nodes,
                        &rpc_load_balancer,
                        &refresh_sleep_duration,
                    ) {
                        warn!("Failed to refresh pubkey to stake map! Error: {err:?}");
                        sleep(refresh_sleep_duration);
                    }
                }
            })
            .unwrap();

        Self { thread_hdl }
    }

    /// Update the stake info when it has elapsed more than the
    /// STAKE_REFRESH_INTERVAL since the last time it was refreshed.
    fn try_refresh_stake_info(
        last_refresh: &mut Option<Instant>,
        shared_staked_nodes: &Arc<RwLock<StakedNodes>>,
        rpc_load_balancer: &Arc<RpcLoadBalancer>,
        refresh_sleep_duration: &Duration,
    ) -> client_error::Result<()> {
        if last_refresh.is_none() || last_refresh.unwrap().elapsed() > STAKE_REFRESH_INTERVAL {
            let client = rpc_load_balancer.rpc_client();
            let vote_accounts = client.get_vote_accounts()?;

            let stake_map = Arc::new(
                vote_accounts
                    .current
                    .iter()
                    .chain(vote_accounts.delinquent.iter())
                    .filter_map(|vote_account| {
                        Some((
                            Pubkey::from_str(&vote_account.node_pubkey).ok()?,
                            vote_account.activated_stake,
                        ))
                    })
                    .collect::<HashMap<Pubkey, u64>>(),
            );

            *last_refresh = Some(Instant::now());
            shared_staked_nodes
                .write()
                .unwrap()
                .update_stake_map(stake_map);
        } else {
            sleep(*refresh_sleep_duration);
        }
        Ok(())
    }

    pub fn join(self) -> thread::Result<()> {
        self.thread_hdl.join()
    }
}
