# Changelog

## 1.0.0 — 2026-07-18

- Corrected the general redundant-coefficient indexing from `A_n ≡ m` to
  `-A_n ≡ m`, equivalently `A_n ≡ -m`, while retaining the correct constant
  coordinate supports `A_n ≡ 0` and `A_n ≡ 1`.
- Replaced the scratch text in the four-root lemma with the exact congruence
  for `a + 1`, proved that `a + 1` is the canonical representative, and gave
  a clean pairwise-distinctness proof.
- Expanded the finite Rogers--Fine proof with the exact summand, certificate,
  single-term identity, interior algebra, initial boundary, and separate final
  boundary used by the Lean source.
- Expanded the tail-reflection proof into a complete finite reindexing and
  complementary-pair calculation.
- Replaced the coefficient-vector overclaim with the verified universal
  classification in `{0,1,2,3}` and recorded exact multiplicities as
  downstream.
- Defined `T_p(1)` before use and stated the two Lean-verified coefficient-sum
  formulas.
- Preserved the corrected Fine-collapse signs, certificate, last boundary,
  and evaluation at `X = 1`.
- Aligned every theorem-status claim with the Lean development and explicitly
  listed exact multiplicities, the mock Gauss-sum lift, and subset-count
  formulas as not yet formalized.
- Added the permanent `Audit.lean` axiom audit and executable `verify.sh`
  release check.
- Added reproducibility instructions, release metadata, dual licensing, and
  the exact author name Joesph D. Burke III.
- Recorded the correction that the cyclotomic product equals `1` for every odd
  order, prime or composite, so it is not a primality test.
