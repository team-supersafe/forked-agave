use {
    criterion::{criterion_group, criterion_main, Criterion},
    rand::{thread_rng, Rng},
    rayon::ThreadPoolBuilder,
    solana_gossip::{
        crds::{Crds, GossipRoute},
        crds_gossip_pull::{CrdsTimeouts, CRDS_GOSSIP_PULL_CRDS_TIMEOUT_MS},
        crds_value::CrdsValue,
    },
    solana_pubkey::Pubkey,
    std::{collections::HashMap, time::Duration},
};

fn bench_find_old_labels(c: &mut Criterion) {
    let thread_pool = ThreadPoolBuilder::new().build().unwrap();
    let mut rng = thread_rng();
    let mut crds = Crds::default();
    let now = CRDS_GOSSIP_PULL_CRDS_TIMEOUT_MS + CRDS_GOSSIP_PULL_CRDS_TIMEOUT_MS / 1000;
    std::iter::repeat_with(|| (CrdsValue::new_rand(&mut rng, None), rng.gen_range(0..now)))
        .take(50_000)
        .for_each(|(v, ts)| assert!(crds.insert(v, ts, GossipRoute::LocalMessage).is_ok()));
    let stakes = HashMap::from([(Pubkey::new_unique(), 1u64)]);
    let timeouts = CrdsTimeouts::new(
        Pubkey::new_unique(),
        CRDS_GOSSIP_PULL_CRDS_TIMEOUT_MS, // default_timeout
        Duration::from_secs(48 * 3600),   // epoch_duration
        &stakes,
    );
    c.bench_function("bench_find_old_labels", |b| {
        b.iter(|| {
            let out = crds.find_old_labels(&thread_pool, now, &timeouts);
            assert!(out.len() > 10);
            assert!(out.len() < 250);
            out
        })
    });
}

criterion_group!(benches, bench_find_old_labels);
criterion_main!(benches);
