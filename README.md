> **Note.** This entire repository was machine-written by AI assistants at the direction of Tom Adamczewski. The Lean proof itself was written by GPT-6 Astra, as described below.

# Erdős problem #1207 (isosceles-free subsets of planar point sets): proof

[![CI](https://github.com/tadamcz/erdos1207/actions/workflows/ci.yml/badge.svg)](https://github.com/tadamcz/erdos1207/actions/workflows/ci.yml)

A machine-checked proof of [Erdős problem #1207](https://www.erdosproblems.com/1207) in Lean 4 with Mathlib. The
proof was found autonomously by a pre-release version of GPT-6 Astra (OpenAI) running in the harness of the
FrontierMath Erdős benchmark (Adamczewski and Bloom, 2026). In this repository, `Challenge.lean` is the short statement a reader audits,
`Solution.lean` proves it, and `Audit.lean` with `scripts/audit.sh` checks that the two statements coincide and that
the proof uses only the standard axioms.

## The result

Take a set of `n` points in `ℝ^d` and consider its largest subset with no isosceles triangle, that is, no three
distinct points among which two of the three pairwise distances agree. Degenerate collinear triples count. Let
`P_d(n)` be the smallest such maximum over all `n`-point sets, so that every `n` points in `ℝ^d` contain `P_d(n)`
points with no isosceles triangle. Erdős [Er80, p. 110] attributes the problem to Riddell and asks for estimates of
`P_d(n)`, in particular whether `P_2(n) < n^{1-c}` for some constant `c > 0`. A subset with all distances distinct
gives `P_d(n) ≥ n^{1/(3d-3) - o(1)}`. Pach and Tardos [PaTa02], with a random deletion argument, give
`P_2(n) ≫ n^{0.432}`. The case `d = 1` is the problem of large progression-free subsets, and the vertices of a
regular polygon show `P_2(n) ≪ r_3(n) = n^{1-o(1)}`, which is not a power saving.

The answer is yes. There is `c > 0` with `P_2(n) < n^{1-c}` for all sufficiently large `n`.

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

### Fidelity

There is no known divergence from the erdosproblems.com statement. `P d n` is the infimum, over `n`-element finsets
of `EuclideanSpace ℝ (Fin d)`, of the supremum of the sizes of their isosceles-free subsets, which is `P_d(n)`. For
every `n` such a finset exists, and the inner set of sizes is nonempty and bounded by `n`, so neither `sInf` nor
`sSup` falls back on its junk value `0`. `IsIsosceles p q r` is
`dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q`, so degenerate collinear triples count as
isosceles, in line with the problem's own remark that the case `d = 1` is the three-term-progression problem. The
conclusion says "for some constant `c > 0` and all sufficiently large `n`", with `n^(1-c)` the real power. The
informal question does not fix the range of `n`, and any `c ≤ 1` forces `P_2(n) ≥ 2` for `n ≥ 2`, so the eventual
quantifier is the natural reading. The value of `c` is existential and is not advertised.

## The proof

`Solution.lean` is an ordinary Lean development of 14,163 lines, 658 theorems and about 1,912 declarations, with no
`sorry`. A mathematician can read it. The argument, in the model's own structure:

1. A geometric reduction. It suffices to exhibit, for each `m`, a configuration `S_m` of complex points with
   `|S_m| ≤ 2^(H·2^m)` in which every isosceles-free subset `A` satisfies `2^(2^m)·|A| ≤ |S_m|`. Disjoint translated
   copies then fill the gaps between sizes, giving the conjecture with `c = 1/(4H)`. This is
   `Erdos1207.power_saving_of_unit_directions` and the replication lemmas around it.
2. Such configurations come from an unbounded tower of totally real, everywhere-unramified degree-2 extensions of
   number fields, embedded in the plane through one complex place. Units of relative norm one supply many directions
   of equal modulus, and an additive-energy bound converts few directions with a controlled sumset into the required
   scarcity of isosceles-free subsets.
3. The tower's existence is reduced to a Golod-Shafarevich-style relation-rank bound, proved through Kummer theory
   and the cohomology of the ideal group because Mathlib has no class field theory, together with an explicit finite
   starting point: the real quartic field `B = ℚ(√5, √D)`, with `D` a product of primes `≡ 1 mod 4`, and a
   multiquadratic unramified extension of it whose first cohomology has dimension at least 254. The endpoint is
   `LargeTowerCriterion.arithmetic_family`, and `erdos_1207` closes with
   `exact LargeInitialGenusCertificate.power_saving`.

Along the way the model also proved, unconditionally, `(log_4225 n + 1)^2 · P_2(n) ≤ 324n`, a `(log n)^2` saving
that does not settle the fixed-power question.

Nobody has refereed this argument. What is checked is that Lean's kernel accepts it and that it uses only the
standard axioms.

## Relation to the literature

The conjectural part of #1207 was settled on 6 July 2026 by Sungchul Lee, Cosmin Pohoata and Daniel G. Zhu, *The
Minkowski grid has robustly many repeated distances* ([arXiv:2607.05374](https://arxiv.org/abs/2607.05374)). They
prove more than #1207: an `n`-point planar set in which every subset `A` of size at least 2 has some distance
repeated `≳ |A|²/n^(1-δ)` times. An isosceles-free set repeats no distance more than `|A|` times, so this bounds
isosceles-free subsets by `n^(1-δ)`, which is #1207. The same inequality also gives a counterexample to the
unit-distance conjecture and a result on subsets with distinct distances.

### What the two arguments share

The two arguments share a frame. Each realizes the point set as a Minkowski grid, a symmetric box in the ring of
integers of a number field of unboundedly high degree with bounded root discriminant, pushed into the plane by a
single embedding. Each rests on the same elementary fact, that an isosceles-free set has at most one point at any
given distance from any given point, and each uses Cauchy-Schwarz to force distance coincidences. The towers are
totally real in each case, and primes congruent to 1 mod 4 appear in each construction.

### Where they differ

The source of the repeated distances differs, and so does the way the tower is obtained.

| | Lee, Pohoata and Zhu | this proof |
|---|---|---|
| plane realization | pairs of elements of a totally real field, via one real embedding | single elements of a mixed-signature field, via one complex place |
| source of repeated distances | a sieve over primes that split completely | units of relative norm one, acting as isometries |
| tower | cited from Hajir, Maire and Ramakrishna | constructed in the file, Golod-Shafarevich style |
| class group | avoided | used throughout |

Lee, Pohoata and Zhu fix primes `≡ 1 mod 4` that split completely in the field. Since `x² + y²` factors into
conjugate linear forms modulo each prime above them, Cauchy-Schwarz over the cosets of a congruence subgroup forces
many pairs whose squared distance is divisible by a large ideal. Squared distances lie in a small box, so pigeonhole
yields a popular value. This proof builds a group of isometries. It adjoins a square root of an element of square 5,
which has a negative real conjugate, so the extension is mixed-signature and has a complex place. Units of relative
norm one land on the unit circle there and supply a large set of directions of equal modulus, and translating by them
repeats a distance by construction. The remaining work is an additive-energy bound with controlled sumset growth,
in `DirectionCounting` and `SumsetGrowth` in `Solution.lean`.

The towers differ for a reason visible in the file. Lee, Pohoata and Zhu need bounded root discriminant together
with infinitely many completely split primes, and take both from [HMR21]. They note that their proof avoids the
class group. This proof uses neither split primes nor Chebotarev, which appear nowhere in it. It needs an infinite
unramified totally real 2-tower, along which bounded root discriminant is automatic. Mathlib has no class field
theory, so the proof establishes a relation-rank bound through Kummer theory and the cohomology of the ideal group,
and supplies an explicit genus-theoretic starting point over the real quartic field `ℚ(√5, √D)`, with `D` a product
of primes `≡ 1 mod 4`, bounding the class 2-rank by a crude class-number estimate. The 1 mod 4 primes play unrelated
roles in the two proofs: splitting behaviour in one, unramifiedness at 2 in the other.

### Lineage

Lee, Pohoata and Zhu describe their construction as a "vertical amplification" of an earlier OpenAI result, an
OpenAI model's disproof of the unit-distance conjecture
([Ope26](https://openai.com/index/model-disproves-discrete-geometry-conjecture/); Alon, Bloom, Gowers, Litt, Sawin,
Shankar, Tsimerman, Wang and Wood, *Remarks on the disproof of the unit distance conjecture*,
[arXiv:2605.20695](https://arxiv.org/abs/2605.20695)), which introduced the high-degree Minkowski grid as a
counterexample device. Their acknowledgments record that the collaboration began from a manuscript of Lee's produced
with ChatGPT, combining that number-field-tower idea with the combinatorial sieve of Croot, Mao, Pohoata, Sheffer and
Yip. The proof in this repository arrives at the same amplification idea by a different mechanism, and it had access
to none of this. Every item in the chain dates from May 2026 or later, after GPT-6 Astra's 30 April 2026 knowledge
cutoff, so none of it was in the model's training data.

There is a caveat on independence. OpenAI has described its 2026 mathematical results as the work of an internal
version of Astra. If the unit-distance construction was among them, then one model reached for the same idea in two
separate runs. The sources available here do not settle which model produced that construction.

## Provenance

### Run

The proof comes from the eval set `erdos-ultima-alpha-1000usd`, sample `Erdos1207.erdos_1207` (uuid
`cTsYA4Q65LmZ9kjKMAWq6d`), a re-run started on 3 September and finished on 5 September 2026 after the sample's first
attempt died on an infrastructure error. The configuration was the harness's larger-budget one: a basic ReAct agent
with no subagents, no memory and no literature snapshot, in a network-isolated Docker container with a Lean 4 v4.27.0
toolchain, Mathlib, SageMath and Python. No human saw or steered the proof search.

### Statement

The problem had no statement in Formal Conjectures. The statement was produced by the benchmark authors'
autoformalization pipeline. The file the model received is
[`apn/data/erdos_autoformalized/Isolated/Erdos1207.erdos_1207.lean`](https://github.com/epoch-research/LeanOpenProblems/blob/8fa3b4c6ee5e6f0ee25d027b6f110f20787db977/apn/data/erdos_autoformalized/Isolated/Erdos1207.erdos_1207.lean)
at commit `8fa3b4c6`.

### Cost

Cost is computed from the attempt's token counts at GPT-6 Astra's standard rates as provided by OpenAI on
3 September 2026: $10 per million input tokens, $50 per million output, $1 per million cache-read, $12.50 per million
cache-write. The harness itself metered spend at stand-in GPT-5.6 Sol prices. Working time is the harness's
`working_time`, which excludes waits on API retries. Both figures cover the whole attempt, which continued after the
proof in this repository was complete. The proof was finished at 27 h 42 m and $221 of metered spend.

| Attempt | Cost | Working time | Tokens, millions (input / output / cache read / cache write) |
|---|---|---|---|
| ReAct agent, larger budget, 3-5 Sep 2026 (re-run) | $549 | 36.6 h | 0.25 / 2.7 / 215 / 15.5 |

Two other attempts on this statement in the same eval set did not resolve it. One ran the full 96-hour working-time
limit to about $800, and one was lost to a Kubernetes error at about $367 after 47 hours. Both left the `sorry` in
place.

## Toolchain

This repository pins Lean v4.27.0 and Mathlib `a3a10db0`, the v4.27.0 release, which is what the proof was written
against.

### Why Mathlib v4.28.0 was not adopted

Porting to Mathlib v4.28.0 was tried and abandoned. Against v4.28.0 the file produces a single error, and it cannot
be fixed mechanically. Mathlib refactored the inertia-group API: where the proof rewrites with a lemma about
`(Submodule.toAddSubgroup P).inertia Gal(M/K)`, v4.28.0 states the same object as `Ideal.inertia Gal(M/K) P`. The
rewrite finds no occurrence of its pattern, and the enclosing theorem degrades to `sorryAx`. Repairing it would mean
editing the model's mathematics, and further breakages may sit behind the first. So the pin stays and the proof
remains the model's own work.

## Repository layout

- `Challenge.lean` is the statement surface. It holds the definitions copied verbatim from the benchmark statement and the compared theorem with `sorry`.
- `Solution.lean` is the whole of the AI-written proof. There is one resolution, so it is a single file with no library of imported modules.
- `Audit.lean` and `scripts/audit.sh` check that `Challenge.lean` and `Solution.lean` give `Erdos1207.erdos_1207` the same fully explicit type, and that the proved theorem depends on no axioms beyond `propext`, `Quot.sound` and `Classical.choice`. Comparator itself cannot run at this toolchain. It is built for Lean v4.33, and the oldest `lean4export` release is v4.29.1.
- `comparator.json` is the Comparator configuration naming `Erdos1207.erdos_1207`. It is declarative and is not executed.
- `formalization.yaml` is structured metadata in the mathlib-initiative v0.4 format. `scripts/validate-formalization.rb` checks it.
- `provenance/` holds the SHA-256 of the file the harness captured and the unified diff from it to `Solution.lean`.
- `.github/workflows/ci.yml` builds and audits the project, validates the metadata, and checks that the provenance diff round-trips to the recorded hash.

## Edits relative to the benchmark output

`Solution.lean` is the model's file as the harness captured it, with two mechanical changes. The diff is in
`provenance/`, and CI checks that reversing it reproduces the recorded SHA-256
(`95e2e33b657083b72896f381917a3a857ef32f010f21ab98ba1b92f85297e151`). No mathematics was touched, and the toolchain
was not changed.

- Line 1, `import FormalConjecturesUtil`, became `import Mathlib`.
- Six declarations that this import supplied, and that Mathlib lacks, were inserted, copied verbatim from
  [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) (Google DeepMind, Apache-2.0) at commit
  `9cbe1d3c12998c786b7c2cd99ce28a21b6631f66`. `Set.Triplewise` and `IsIsosceles` are used by the statement itself.
  `Nat.Prime.squarefree`, `QuadraticAlgebra.instField'`, `QuadraticAlgebra.instIsQuadraticExtension` and
  `Algebra.IsQuadraticExtension.to_numberField` are used inside the proof.

There are no other changes. Every `set_option` in the file is the model's own, and they are ordinary
`maxHeartbeats`, `maxRecDepth` and `synthInstance.maxHeartbeats` bumps.

## Verification

```sh
lake exe cache get
lake build          # builds the proof and runs Audit.lean; needs about 10 GB of memory
ruby scripts/validate-formalization.rb
./scripts/audit.sh  # compares the two environments' statements and prints the axioms
```

CI runs the same checks.

## Licence and attribution

This repository snapshot is licensed under the Apache License 2.0 (see `LICENSE`). Six definitions it reproduces are
from Formal Conjectures, © The Formal Conjectures Authors, Apache-2.0 (see `NOTICE`). The benchmark statement is from
the FrontierMath Erdős benchmark (Adamczewski and Bloom; LeanOpenProblems, MIT licence). Cited papers,
erdosproblems.com and Mathlib retain their own licences.
