# Phase 7 increasing-loss hypothesis closure

## Outcome

The remaining hypothesis strengthening in `tailloss` has been removed. The
master-facing generic and class-indexed declarations assume only that
`g : ℝ → ℝ` is non-decreasing on `[0,∞)`, together with the manuscript's
boundedness-or-initial-integrability alternative. They do not assume
`Measurable g`.

## Proof device

Define

```text
g₊(r) = g(max r 0).
```

If `g` is non-decreasing on `[0,∞)`, then `g₊` is non-decreasing on all of
`ℝ`, so it is Borel measurable. Every discrepancy `Rₙ` is non-negative, hence
`g₊(Rₙ) = g(Rₙ)` pointwise. The existing measurable increasing-loss machinery
can therefore be applied to `g₊`, and its conclusion rewritten exactly in
terms of `g`.

The new generic declarations are:

- `SequentialLearning.conditional_increasing_loss_order_nonnegative`;
- `SequentialLearning.conditional_increasing_loss_supermartingale_nonnegative`.

The existing class-facing name
`SequentialLearning.HypotheticalSequentialEstimand.StructuralPresentation.monotoneClass_conditional_increasing_loss_supermartingale`
now calls the closed theorem and likewise has no global measurability premise.

## Audit boundary

`LossInterfaceAudit.lean` prints the three exact master-facing types. Its
script rejects a reintroduced `hgMeas` binder. The manuscript-alignment check
rejects the former Borel-measurability assumption and requires the constant-
left extension argument. The original 41 source modules remain byte-for-byte
unchanged.

The reverse flag-space Wasserstein equality was deliberately outside this
phase. It is subsequently closed unconditionally in
`docs/PHASE8_FLAG_WASSERSTEIN.md`.
