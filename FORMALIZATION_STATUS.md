# Formalization status

## Release baseline

- Release: `v1.0.0` (2026-07-18).
- Lean: `v4.31.0`, commit
  `68218e876d2a38b1985b8590fff244a83c321783`.
- Mathlib: `v4.31.0`, commit
  `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`.
- The development contains no `sorry`, `admit`, custom `axiom`, `sorryAx`, or
  proof by `native_decide`.

## Completed and Lean-verified

- Central theorem: `MockTheta.c0_T_eq_three` proves `c_0(T_p)=3` for every
  prime `p ≥ 7` in every characteristic-zero cyclotomic extension containing
  a primitive `p`-th root.
- Directive-compatible alias: `MockTheta.constantCoeff_T_eq_three`.
- Weighted formula: `MockTheta.weighted_formula` (with the reverse-Fine form
  `MockTheta.weighted_formula_reverse`).
- Finite Fine collapse: `MockTheta.finiteFine`, `MockTheta.fineCollapse`, and
  `MockTheta.reverseFine`.
- Finite Rogers--Fine identity: `MockTheta.finiteRogersFine`.
- Coefficient-sum formulas:
  `MockTheta.TAtOne_of_eq_six_mul_add_one` and
  `MockTheta.TAtOne_of_eq_six_mul_add_five`.
- Algebra-trace formulas: `MockTheta.trace_T_of_eq_six_mul_add_one` and
  `MockTheta.trace_T_of_eq_six_mul_add_five`.
- Universal coefficient classification: `MockTheta.cCoeff_T_mem_four` proves
  that every power-basis coefficient belongs to `{0,1,2,3}`.
- Regression cases: typechecked examples for `p = 7, 11, 13` in
  `MockTheta.AuditExamples`.
- Supporting results include `MockTheta.fullCycleProd`,
  `MockTheta.cyclotomicDefect`, and the redundant-to-power-basis coordinate
  conversion.

All Fine and Rogers--Fine steps are finite polynomial identities. Formal
differentiation replaces analytic continuation and l'Hôpital's rule.

## Downstream and not yet formalized

- Exact coefficient multiplicities.
- The characteristic-zero mock Gauss-sum lift.
- Subset-count formulas and corollaries.

These statements are not assumed by the central theorem, coefficient-sum
formulas, algebra-trace formulas, or universal coefficient classification.

## Corrected product claim

The formerly asserted composite-product/primality-test claim was corrected.
For every odd order `k > 1`, prime or composite,

```text
∏ j in Icc 1 (k - 1), (1 + ζ^j) = 1.
```

Consequently this product cannot distinguish primes from odd composites.

## Release verification

Run from the project root:

```bash
lake build
lake env lean Audit.lean
./verify.sh
```

`Audit.lean` applies `#print axioms` to the principal theorem chain. Its output
contains only `propext`, `Classical.choice`, and `Quot.sound`; it contains no
`sorryAx` or project-defined axiom.
