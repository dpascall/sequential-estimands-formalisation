# Phase 5 manuscript alignment and final audit

## Audit basis and outcome

This audit compares the supplied manuscript text (SHA-256
`d76a328df268fe15a71150bac1714f44366f6c5e92c9cecb128c7baf4c96dd23`) with the
compiled project through Phase 4 and the subsequent same-estimand,
increasing-loss, and flag-space repairs. The resulting aligned manuscript is
`manuscript/Sequential_learning_theory_aligned.tex`.

The aligned manuscript has 46 unique labels. Every label has exactly one row in
`checks/manuscript-label-index.tsv`, and every semicolon-separated declaration
in that row is checked by Lean. The index covers 4 theorems, 10 propositions,
11 lemmas, 9 corollaries, 2 constructions, 2 definitions, 4 equations, 2
remarks, 1 section, and 1 table.

All named results and constructions in the **aligned manuscript** therefore
have compiled counterparts. The same-estimand impossibility theorem, which was
the sole substantive result withdrawn in the initial Phase 5 audit, is now
formalised by the finite flag-lifted rotation construction.

## Editorial decisions

### Measurability of the increasing loss

The statement labelled `tailloss` again assumes only that `g : ℝ → ℝ` is
nondecreasing on `[0,∞)`. The closed Lean interface replaces `g` internally by
the constant-left extension `g_+(r) = g(max r 0)`. This extension is globally
monotone and hence Borel measurable. Since every discrepancy is nonnegative,
`g_+ ∘ R_n = g ∘ R_n` pointwise. Consequently no assumption on the behaviour
or measurability of `g` below zero is required.

### Duplicated class event

The duplicated accidental-equality event in the taxonomy assumptions has been
removed. The remaining three events are equality-achievability,
persistence-achievability, and accidental equality. These are exactly the
three fields represented by `ClassEventsMeasurable`.

### Greatest valid constraint family

The draft's existence assumption has been replaced by the lemma labelled
`greatestfamily`. Lean defines the canonical family as the union of all valid
families, proves that the union is valid, proves it greatest, and proves
uniqueness. This is a theorem under the manuscript's definitions, so retaining
the assumption would be redundant.

### Conditional-law and conditional-expectation representations

The aligned manuscript now records the representations used by the Lean
development:

- a regular conditional distribution is an explicit probability kernel plus
  its `IsRegularConditionalLaw` property;
- comparison theorems quantify over chosen versions and assert their
  conclusions almost surely;
- real conditional expectations use Mathlib's everywhere-defined real
  conditional-expectation version;
- Hilbert conditional means use Bochner conditional expectation;
- nonnegative Frechet risks are first defined in `[0,∞]`, with the master
  second-moment assumption supplying almost-sure finiteness for real-valued
  differences; and
- the absorption-oracle branch package asserts that its mixture is the
  `F_∞`-conditional law and its status-selected kernel is the
  oracle-conditional law.

No master-facing Phase 4 wrapper constructs an RCD from nothing. This matches
the manuscript's stated assumption that the required RCDs exist and avoids a
hidden measurable-space existence hypothesis.

## Differences from the supplied draft

| Topic | Supplied draft | Verified formal status | Resolution |
|---|---|---|---|
| `tailloss` | `g` is only nondecreasing on `[0,∞)` | The original analytic core requires `Measurable g`, but the closed wrapper derives a measurable constant-left extension | Exact manuscript hypothesis restored; no global measurability premise remains at the master-facing boundary. |
| Taxonomy events | Accidental-equality event displayed twice | `ClassEventsMeasurable` has three distinct events | Duplicate removed. |
| Greatest family | Existence and uniqueness assumed | Canonical union exists, is valid and greatest, and is unique | Assumption replaced by a proved lemma. |
| Binary-oracle branches | Wording could require both branch moments even at `p=0` or `p=1` | Closed theorem derives both moments only for `0<p<1`; an unused endpoint branch is irrelevant | Endpoint convention made explicit. No master-level strengthening remains. |
| Flag-space Wasserstein claim | Reverse equality claimed for arbitrary flagged laws | Phase 8 constructs a lift of every projected coupling using conditional Boolean flag kernels | Exact unconditional equality restored; the manuscript qualification has been removed. |
| Flag admissibility | Terminal flag fixed to `0` and measurability implicit | Generic interface uses a designated terminal flag; concrete flags are prefix-compatible, terminal-compatible, and measurable | Manuscript generalized to the exact interface. |
| Rotation construction | Packaged with a latent observation model and used by structural rows | Lean proves the analytic rotation identities abstractly; the compiled witness table is a separate finite construction | Manuscript separates the analytic rotation family from the finite structural witnesses. |
| Witness table | Rows were asserted to be rotation-family members with different paths | Lean's exact `rowValue` table uses horizon 6 and the paths `3,2,1,1,0,0,0` or `1,2,1,1,0,0,0` | Table and proof text replaced by the compiled data. |
| `bothverdicts` | Two observation maps were claimed for one rotation estimand, with a conditional expected increase in one | Lean now gives canonical flag-valued RCDs for the same estimand under both models and proves exact Fréchet values: zero change in Model A and `J=3/340`, `S=44/340`, increase `41/340` in Model B | Exact same-estimand statement restored. |
| `impossibility` | Every non-fixed class was claimed to admit both learning behaviours for the same estimand function | Each of the eight non-fixed classes now has one flag-lifted rotation witness whose `HasClass` proof and both Fréchet-variance verdicts are compiled together | Exact statement restored; the fixed class remains governed by `fixedTarget_learning`. |
| `biasweight` proof | Normalised direction implicitly required a nonzero vector when the bias vanished | Lean uses the zero vector as fallback and proves norm at most one | Manuscript proof corrected; no nontrivial-Hilbert assumption is needed. |

## Unformalised material from the supplied document

The former same-estimand gap is closed. The repair does not reuse
`StructuralWitnesses.witnesses`: it proves `HasClass` afresh for rotation-valued
rows, maps the finite conditional-expectation kernel by the actual flag-valued
stage function, and projects its Fréchet variance to the Hilbert coordinate.
The existing branch bit supplies the independent orthogonal direction, so no
fifth latent bit is needed.

### 1. One packaged version of the opening generative model

The abstract structural API represents the finite horizon, admissible orders,
revealed prefixes, estimand values, terminal value, and prefix compatibility.
`RealizedObservedProcess` derives a capped realised sequence and records its
filtration-adaptedness. It does **not** package the full opening narrative
`Θ ∼ P_π`, `Λ | Θ ∼ Q_Θ`, the raw observations `D_n`, and a proof that
the recorded filtration is definitionally `σ(D_n)` for an arbitrary model.
The finite noisy experiment does construct its own three-stage generated
filtration. Thus the general opening setup remains an informal model schema,
not a single exact Lean construction.

### 2. General RCD existence outside the proved real-valued case

The manuscript assumes the required posterior/RCD kernels exist. The Lean
master theorems accept those kernels and their RCD properties explicitly.
The project does construct the real-valued conditional-law kernels used by the
tail results, but it does not prove a universal RCD-existence theorem for every
measurable separable pseudometric target in the opening setup. This is not a
mismatch after the representation convention was added; it is the stated
boundary of the result.

## Hypothesis-strength audit

- The closed displacement results no longer expose the auxiliary
  `Wasserstein2LawMeasurable` premise. Polish-completion measurability is proved
  internally.
- The class-facing tail and MSE wrappers no longer expose separate
  monotonicity, absorbing-coverage, step-order, or fixedness assumptions; these
  follow from `HasClass`. `RealizedObservedProcess` still records measurable,
  adapted, and `L²` data that correspond to the manuscript's analytic process
  assumptions.
- The master-facing increasing-loss order and supermartingale wrappers no
  longer expose `Measurable g`; monotonicity on `[0,∞)` supplies measurability
  through `nonnegativeExtension`.
- `threeway`, `oraclestrict`, and `oraclehilbert` expose RCD existence, event
  measurability, target measurability, and the master square moment, but no
  implementation-level branch-finiteness, branch-`L²`, finite-branch, or
  kernel-constructor assumption.
- The exact flag-space Wasserstein theorem no longer exposes `CouplingsLift`.
  Boolean standard-Borel disintegration constructs the two conditional flag
  kernels internally and lifts every projected coupling at equal cost.
- Some Lean results are stronger than the manuscript: `biasweight` works for
  a possibly zero-dimensional Hilbert space, and the greatest-family theorem
  eliminates an assumption rather than adding one.

## Verification boundary

`scripts/check_manuscript_alignment.sh` checks all 46 labels, compiles every
indexed declaration, and verifies the mandated editorial and hypothesis
changes, including unconditional flag-space Wasserstein equality.
`scripts/check_all.sh` additionally checks source integrity of the original 41
modules, rejects placeholders, builds the aggregate project, runs the complete
axiom audit, and runs the Phase 1--4, same-estimand, increasing-loss, and
flag-space interface-leak audits.

The aligned manuscript was also checked structurally for balanced LaTeX
environments and braces. A PDF compile could not be used as a release gate in
the verification container because its TeX installation lacks the
`pdflatex.fmt` format file; this does not affect the Lean build or declaration
audit.
