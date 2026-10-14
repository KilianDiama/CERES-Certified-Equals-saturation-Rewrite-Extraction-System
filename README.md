NOYAU v17
A sound-first e-graph rewriting kernel with proof-carrying certificates, multi-objective Pareto extraction, and algebraic normalization over ℤ/2⁶⁴.

https://img.shields.io/badge/rust-stable-orange https://img.shields.io/badge/license-MIT-blue https://img.shields.io/badge/status-research--kernel-red

What it is
NOYAU is a deterministic symbolic optimization kernel: it explores equivalence classes of expressions via e-graph rewriting, proves identities algebraically, extracts Pareto-optimal representations under multiple cost models, and emits independently verifiable certificates for every union.

Not a wrapper. Not a heuristic. A rewrite engine whose every transformation can be rechecked by a pure verifier that trusts neither the scheduler nor the search.

Core capabilities
E-graph engine — union-find with history, hashconsing, congruence closure, constant folding, dirty-class propagation.

Proof-carrying unions — every merge carries a Proof (Refl, Sym, Trans, Congr, Rule, ConstFold) re-verified before mutation by check_proof + expr_is_in_class.

Algebraic prover — polynomial normalization over ℤ/2⁶⁴ for Add/Mul/Sub, canonical forms for Xor/And/Or, with monomial, degree, and fuel budgets.

Trusted vs. Experimental rules — trusted rules must pass prove_rule at registration; experimental rules can never enter the certified graph.

AC matching — complete bipartite matching for commutative ops, ordered matching for the rest; arity-strict by design (no unsound subset matching).

Multi-objective Pareto extraction — tri-objective (energy, size, depth) frontier per class, with monotone fixpoint (ever_seen) and explicit truncation markers.

Three cost models — CPU, GPU, FPGA; pluggable via CostModel.

Five static analyses — constant, size, interval, bit-width, intrinsic cost — with checked_* arithmetic and saturated bitmasks.

Parallel matching — fixed-size scoped thread pool, no thread-per-class explosion.

Backoff scheduler — egg-style node-budget backoff per rule.

Shortest explanation — BFS over the union-record graph, returning the actual chain of proof records.

128-bit fingerprints — full Fingerprint as PatternId, no truncation, no silent cache collisions.

Hard resource budgets — time, nodes, matches, polled inside inner loops.

What makes it different
Property	NOYAU v17
Certified unions	✅ proof verified before mutation
Soundness-first	✅ unsound optimizations removed, not patched
Determinism	✅ pure verifier, no scheduler trust
Multi-objective	✅ Pareto frontier + witness reconstruction
Algebraic reasoning	✅ sound mod 2⁶⁴, budgeted, honest Unknown
Scale	✅ bounded threads, budgets, backoff
Most e-graphs say "we found it." NOYAU says "here is the proof, check it yourself."

Quick start
bash
rustc -O kernel_v17.rs -o kernel_v17 && ./kernel_v17
rustc --test kernel_v17.rs -o kernel_v17_tests && ./kernel_v17_tests
rust
let mut g = EGraph::new();
g.scheduler.add_trusted("x+0→x",
    Pat::Op(Op::Add, vec![Pat::Var(0), Pat::Const(0)]),
    Pat::Var(0));

let x = g.make_const_u64(42);
let z = g.make_const_u64(0);
let xp0 = g.make_node(Op::Add, vec![x, z], vec![]);

Runner::new().with_iter_limit(50).run(&mut g);

let (expr, cost) = g.extract_best(xp0, &CpuCost, ExtractionMode::Exact).unwrap();
for rec in g.explain_shortest(xp0, x) {
    g.verify_record(&rec).expect("certificate must hold");
}
Verified properties (tests)
bitmask_upper(x) >= x for all sampled x.

range_add never underflows or overflows silently.

Prover rejects x + 1 = x.

Forged certificates (no proof, wrong rule) are rejected.

Arities mismatch → zero matches (no fake theorems).

AC matching finds all permutations on equal arity.

explain_shortest returns a non-empty path on a real rewrite.

Differential prover soundness vs. a u64 evaluator.

Strict 8-byte payload validation.

Documented limits
Congruence proofs use Refl-based Congr + structural class check — not yet full Nieuwenhuis–Olivera proof-producing closure.

No variadic patterns (no VarStar); the price of sound AC matching.

Exact Pareto termination depends on the cost model; Bounded mode is the safe default.

Prover is sound, incomplete — no bit-level reasoning, no distributivity over Xor.

Proofs are in-memory; serialization to an external format is roadmap.

Philosophy
A sophisticated engine may explore a million transformations.
The verifier should need only a handful of rules and one proof.

NOYAU is built so that search can be heuristic and certification stays strict.

Keywords: e-graph · equality saturation · rewriting · proof-carrying code · Pareto extraction · algebraic normalization · bitvector arithmetic · certified optimization · soundness-first · Rust
