use criterion::{black_box, criterion_group, criterion_main, Criterion};
use quisquislib::{
    accounts::{Account, Prover},
    pedersen::vectorpedersen::VectorPedersenGens,
    ristretto::RistrettoPublicKey,
    keys::{SecretKey, PublicKey},
    shuffle::{
        Shuffle, ShuffleProof,
    },
};
use quisquislib::shuffle::ROWS;
use merlin::Transcript;
use rand::thread_rng;
use bulletproofs::PedersenGens;

fn create_shuffle_proof_benchmark(c: &mut Criterion) {
    c.bench_function("create_shuffle_proof", |b| {
        b.iter(|| {
            // Setup test data
            let mut rng = thread_rng();
            let mut account_vector: Vec<Account> = Vec::new();
            for _ in 0..9 {
                let sk: SecretKey = SecretKey::random(&mut rng);
                let pk = RistrettoPublicKey::from_secret_key(&sk, &mut rng);
                let (acc, _) = Account::generate_account(pk);
                account_vector.push(acc);
            }

            let shuffle = Shuffle::input_shuffle(&account_vector).unwrap();
            let pc_gens = PedersenGens::default();
            let xpc_gens = VectorPedersenGens::new(ROWS + 1);
            let mut transcript = Transcript::new(b"ShuffleProof");
            let mut prover = Prover::new(b"Shuffle", &mut transcript);

            // Benchmark this part
            black_box(ShuffleProof::create_shuffle_proof(
                &mut prover, &shuffle, &pc_gens, &xpc_gens,
            ));
        });
    });
}

criterion_group!(benches, create_shuffle_proof_benchmark);
criterion_main!(benches);
