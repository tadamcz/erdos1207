> **Note.** This entire repository was machine-written by AI assistants at the direction of Tom Adamczewski. The Lean proof itself was written by GPT-6 Astra, as described below.

# Erdős problem #1207 (isosceles-free subsets of planar point sets): proof

[![CI](https://github.com/tadamcz/erdos1207/actions/workflows/ci.yml/badge.svg)](https://github.com/tadamcz/erdos1207/actions/workflows/ci.yml)

Machine-checked proof of [Erdős problem #1207](https://www.erdosproblems.com/1207) in Lean 4 with Mathlib, found
autonomously by a pre-release version of **GPT-6 Astra** (OpenAI) in the harness of the **FrontierMath Erdős**
benchmark (Adamczewski and Bloom, 2026). The repository follows the layout of the
[Palomar registry](https://palomar-registry.org/) template: `Challenge.lean` is the small statement a reader audits,
`Solution.lean` proves it, and `Audit.lean` with `scripts/audit.sh` checks that the two statements coincide and that
only the standard axioms are used.

One thing about this result should be said at the outset: **it was already known**. The same statement was proved in
the literature two months before this run, and the model could not have known that. See "Relation to the
literature".

## The result

For a set of `n` points in `ℝ^d`, consider its largest subset containing no isosceles triangle, meaning no three
distinct points two of whose three pairwise distances are equal (degenerate, collinear triples count). Let `P_d(n)`
be the least such maximum over all `n`-point sets, so that every `n` points in `ℝ^d` contain `P_d(n)` points with no
isosceles triangle. Erdős [Er80, p. 110] attributes the problem to Riddell and asks for estimates of `P_d(n)`; in
particular, is it true that `P_2(n) < n^{1-c}` for some constant `c > 0`? A subset with all distances distinct gives
`P_d(n) ≥ n^{1/(3d-3) - o(1)}`, and Pach and Tardos [PaTa02] with a random deletion argument give
`P_2(n) ≫ n^{0.432}`. The case `d = 1` is the problem of large progression-free subsets, and the vertices of a
regular polygon show `P_2(n) ≪ r_3(n) = n^{1-o(1)}`, which is not a power saving.

The answer is **yes**: there is `c > 0` with `P_2(n) < n^{1-c}` for all sufficiently large `n`.

The compared declaration, from `Challenge.lean`:

```lean
theorem erdos_1207 :
    (∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (P 2 n : ℝ) < (n : ℝ) ^ (1 - c)) := by
  sorry
```

with `P` and `IsIsoscelesFree` as in the benchmark statement:

```lean
def IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z => ¬ IsIsosceles x y z

noncomputable def P (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset (EuclideanSpace ℝ (Fin d)), S.card = n ∧
    m = sSup {k : ℕ | ∃ A : Finset (EuclideanSpace ℝ (Fin d)),
      A ⊆ S ∧ IsIsoscelesFree (A : Set (EuclideanSpace ℝ (Fin d))) ∧ A.card = k}}
```

**Fidelity.** Relative to the erdosproblems.com statement there is no known divergence. `P d n` is the infimum over
`n`-element finsets of `EuclideanSpace ℝ (Fin d)` of the supremum of the cardinalities of their isosceles-free
subsets, which is exactly `P_d(n)`: for every `n` such a finset exists, and the inner set of cardinalities is
nonempty and bounded by `n`, so neither `sInf` nor `sSup` falls back on its junk value `0`. `IsIsosceles p q r` is
`dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q`, so degenerate collinear triples count as
isosceles, which matches the problem's own remark that the case `d = 1` is the three-term-progression problem. The
conclusion reads "for some constant `c > 0` and all sufficiently large `n`", with `n^(1-c)` the real power; the
informal question does not pin down the range of `n`, and since any `c ≤ 1` forces `P_2(n) ≥ 2` for `n ≥ 2`, the
eventual quantifier is the natural reading. The value of `c` is existential and is not advertised.

## The proof

`Solution.lean` is an ordinary Lean development: 14,163 lines, 658 theorems, and about 1,912 declarations in all,
with no `sorry`. It is readable, and a mathematician can audit it. The argument, in the model's own structure:

1. A geometric reduction. It suffices to exhibit, for each `m`, a configuration `S_m` of complex points with
   `|S_m| ≤ 2^(H·2^m)` in which every isosceles-free subset `A` satisfies `2^(2^m)·|A| ≤ |S_m|`; disjoint translated
   copies then fill the gaps between sizes, giving the conjecture with `c = 1/(4H)`. This is
   `Erdos1207.power_saving_of_unit_directions` and the replication lemmas around it.
2. Such configurations come from an unbounded tower of totally real, everywhere-unramified degree-2 extensions of
   number fields, embedded in the plane through one complex place. Relative norm-one units supply many directions of
   equal modulus, and an additive-energy bound turns "few directions, controlled sumset" into the required scarcity
   of isosceles-free subsets.
3. The tower's existence is reduced to a Golod-Shafarevich-style relation-rank bound, obtained through Kummer theory
   and the cohomology of the ideal group rather than class field theory (which Mathlib lacks), plus an explicit
   finite starting certificate: a real quartic base `B = ℚ(√5, √D)` with `D` a product of primes `≡ 1 mod 4`, and a
   multiquadratic unramified extension of it whose first cohomology has dimension at least 254. The endpoint is
   `LargeTowerCriterion.arithmetic_family`, and `erdos_1207` closes with
   `exact LargeInitialGenusCertificate.power_saving`.

Along the way the model also proved, unconditionally, `(log_4225 n + 1)^2 · P_2(n) ≤ 324n`, a `(log n)^2` saving
that does not settle the fixed-power question.

Nobody has refereed this argument. What is checked is that Lean's kernel accepts it and that it uses only the
standard axioms.

## Relation to the literature

The conjectural part of #1207 was settled on 6 July 2026 by Sungchul Lee, Cosmin Pohoata and Daniel G. Zhu, *The
Minkowski grid has robustly many repeated distances* ([arXiv:2607.05374](https://arxiv.org/abs/2607.05374)), whose
abstract states that their construction "confirms a conjecture of Erdős from 1980". Their route is also
number-theoretic, using the Minkowski embedding of algebraic integers, but the relation between the two arguments
has not been worked out.

The model cannot have drawn on that paper. It appeared on 6 July 2026, after GPT-6 Astra's 30 April 2026 knowledge
cutoff, so it was not in the model's training data.

## Provenance

**Run.** Eval set `erdos-ultima-alpha-1000usd`, sample `Erdos1207.erdos_1207` (uuid `cTsYA4Q65LmZ9kjKMAWq6d`), a
re-run started 3 September and finished 5 September 2026 after the sample's first attempt died on an infrastructure
error. The configuration was the harness's larger-budget one: a basic ReAct agent, no subagents, no memory, no
literature snapshot, in a network-isolated Docker container with a Lean 4 v4.27.0 toolchain, Mathlib, SageMath and
Python. No human saw or steered the proof search.

**Statement.** The problem had no statement in Formal Conjectures. The statement was produced by the benchmark
authors' autoformalization pipeline; the file the model received is
[`apn/data/erdos_autoformalized/Isolated/Erdos1207.erdos_1207.lean`](https://github.com/epoch-research/LeanOpenProblems/blob/8fa3b4c6ee5e6f0ee25d027b6f110f20787db977/apn/data/erdos_autoformalized/Isolated/Erdos1207.erdos_1207.lean)
at commit `8fa3b4c6`.

**Cost.** Computed from the attempt's exact token counts at GPT-6 Astra's standard rates as provided by OpenAI on
3 September 2026 ($10 per million input tokens, $50 per million output, $1 per million cache-read, $12.50 per million
cache-write). The harness itself metered spend at stand-in GPT-5.6 Sol prices. Working time is the harness's
`working_time`, excluding waits on API retries. Both figures are for the whole attempt, which continued after the
proof in this repository was complete; the proof was finished at 27 h 42 m and $221 of metered spend.

| Attempt | Cost | Working time | Tokens, millions (input / output / cache read / cache write) |
|---|---|---|---|
| ReAct agent, larger budget, 3-5 Sep 2026 (re-run) | $549 | 36.6 h | 0.25 / 2.7 / 215 / 15.5 |

Two other attempts on this statement in the same eval set did not resolve it: one ran the full 96-hour working-time
limit to about $800, and one was lost to a Kubernetes error at about $367 after 47 hours. Both left the `sorry` in
place.

## Toolchain

This repository pins **Lean v4.27.0 and Mathlib `a3a10db0`** (the v4.27.0 release), which is what the proof was
written against. That is a deliberate departure from the sibling repositories in this series, which move to the
oldest Mathlib the Palomar registry accepts.

**Why the toolchain is not moved.** Porting to Mathlib v4.28.0 was tried and abandoned. Against v4.28.0 this file
produces exactly one error, and it is not one that can be fixed mechanically: Mathlib refactored the inertia-group
API, so where the proof rewrites with a lemma about `(Submodule.toAddSubgroup P).inertia Gal(M/K)`, v4.28.0 states
the same object as `Ideal.inertia Gal(M/K) P`. The rewrite finds no occurrence of its pattern, and the enclosing
theorem degrades to `sorryAx`. Repairing it means editing the model's mathematics rather than mechanically adapting
it, and further breakages may be masked behind the first, so the pin stays and the proof remains the model's own
work.

## Repository layout

- `Challenge.lean` — the statement surface: the definitions copied verbatim from the benchmark statement, and the compared theorem with `sorry`.
- `Solution.lean` — the AI-written proof, the whole of it. There is only one resolution, so it is a single file rather than a library of imported modules.
- `Audit.lean`, `scripts/audit.sh` — check that `Challenge.lean` and `Solution.lean` give `Erdos1207.erdos_1207` the same fully explicit type, and that the proved theorem depends on no axioms beyond `propext`, `Quot.sound` and `Classical.choice`. Comparator itself cannot run at this toolchain: it is built for Lean v4.33 and the oldest `lean4export` release is v4.29.1.
- `comparator.json` — Comparator configuration naming `Erdos1207.erdos_1207`; declarative only, not executed.
- `formalization.yaml` — structured metadata in the mathlib-initiative v0.4 format; `scripts/validate-formalization.rb` checks it.
- `provenance/` — the SHA-256 of the file the harness captured and the unified diff from it to `Solution.lean`.
- `.github/workflows/ci.yml` — builds and audits the project, validates the metadata, and checks the provenance diff round-trips to the recorded hash.

## Edits relative to the benchmark output

`Solution.lean` is the model's file exactly as the harness captured it, with only the following two mechanical
changes; the exact diff is in `provenance/`, and CI checks that reversing it reproduces the recorded SHA-256
(`95e2e33b657083b72896f381917a3a857ef32f010f21ab98ba1b92f85297e151`). No mathematics was touched, and the toolchain
was not changed.

- line 1: `import FormalConjecturesUtil` → `import Mathlib`
- inserted the six declarations that `import` supplied which are not in Mathlib, copied verbatim from
  [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) (Google DeepMind, Apache-2.0) at commit
  `9cbe1d3c12998c786b7c2cd99ce28a21b6631f66`: `Set.Triplewise` and `IsIsosceles`, used by the statement itself, and
  `Nat.Prime.squarefree`, `QuadraticAlgebra.instField'`, `QuadraticAlgebra.instIsQuadraticExtension` and
  `Algebra.IsQuadraticExtension.to_numberField`, used inside the proof
- no other changes; every `set_option` in the file is the model's own, and they are ordinary `maxHeartbeats`,
  `maxRecDepth` and `synthInstance.maxHeartbeats` bumps

## Verification

```sh
lake exe cache get
lake build          # builds the proof and runs Audit.lean; needs about 10 GB of memory
ruby scripts/validate-formalization.rb
./scripts/audit.sh  # compares the two environments' statements and prints the axioms
```

CI runs the same checks. This repository is prepared for submission to Palomar through the
[submission form](https://submit.palomar-registry.org/) with the full commit SHA; registration is a separate step by
the maintainer, and a submitter should be aware that the toolchain pin and the missing Comparator run may not meet
the registry's requirements.

## Licence and attribution

This repository snapshot is licensed under the Apache License 2.0 (see `LICENSE`). Six definitions it reproduces are
from Formal Conjectures, © The Formal Conjectures Authors, Apache-2.0 (see `NOTICE`). The benchmark statement is from
the FrontierMath Erdős benchmark (Adamczewski and Bloom; LeanOpenProblems, MIT licence). Cited papers,
erdosproblems.com and Mathlib retain their own licences.
