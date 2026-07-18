# Cyclotomic Mock-Theta Constant

This repository contains Joesph D. Burke III's paper *An Exact
Rogers--Fine Proof that the Cyclotomic Mock-Theta Constant Satisfies
`c_0(T_p)=3`* and its companion Lean 4 formalization.

For every prime `p ≥ 7` and every primitive `p`-th root of unity `ζ`, the
central result proves that the constant power-basis coordinate of the finite
cyclotomic mock-theta value `T p ζ` is `3`.

## Reproducing the Lean verification

The project is pinned by `lean-toolchain` to Lean and Mathlib `v4.31.0`.
From the repository root, run:

```bash
lake build
lake env lean Audit.lean
./verify.sh
```

On a clean source archive, Lake downloads the dependencies recorded in
`lake-manifest.json`; the resulting `.lake/` directory is a local build cache
and is not part of the Zenodo source archive.

`verify.sh` builds the project, rejects Lean placeholders, custom axiom
declarations, `sorryAx`, and `native_decide`, and then runs the permanent axiom
audit. The principal results depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

## Reproducing the paper

A standard TeX Live installation with `pdflatex` is sufficient. Run twice so
that all internal references and the table of contents settle:

```bash
pdflatex c0_proof.tex
pdflatex c0_proof.tex
```

The generated file is `c0_proof.pdf`. The bibliography is embedded in the
LaTeX source, so no separate BibTeX step is required.

## Main Lean results

- `MockTheta.fullCycleProd` and `MockTheta.cyclotomicDefect`
- `MockTheta.finiteFine`, `MockTheta.fineCollapse`, and
  `MockTheta.reverseFine`
- `MockTheta.finiteRogersFine`
- `MockTheta.weighted_formula`
- `MockTheta.c0_T_eq_three`
- `MockTheta.constantCoeff_T_eq_three`
- `MockTheta.TAtOne_of_eq_six_mul_add_one` and
  `MockTheta.TAtOne_of_eq_six_mul_add_five`
- `MockTheta.trace_T_of_eq_six_mul_add_one` and
  `MockTheta.trace_T_of_eq_six_mul_add_five`
- `MockTheta.cCoeff_T_mem_four`
- typechecked regression cases for `p = 7, 11, 13` in
  `MockTheta.AuditExamples`

## Repository structure

- `MockTheta/` — the Lean modules, from cyclotomic products through the
  coordinate and trace consequences
- `MockTheta.lean` — the library's root import
- `Audit.lean` — permanent `#print axioms` audit
- `verify.sh` — release verification entry point
- `c0_proof.tex` and `c0_proof.pdf` — paper source and compiled paper
- `FORMALIZATION_STATUS.md` — exact completed/downstream theorem ledger
- `CITATION.cff` and `CHANGELOG.md` — release metadata
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain` — reproducible
  Lean project configuration

## Formalization scope

Formalized results include the finite Fine collapse, the finite Rogers--Fine
identity, the weighted formula, `c_0(T_p)=3`, the coefficient-sum formulas,
the algebra-trace formulas, the universal classification of every
power-basis coefficient in `{0,1,2,3}`, and the small-prime regression cases.

Not yet formalized are exact coefficient multiplicities, the
characteristic-zero mock Gauss-sum lift, and the subset-count formulas. No
downstream statement is assumed in the proof of the central theorem.

The formerly asserted product-based primality test has also been corrected:
the relevant cyclotomic product equals `1` for every odd order, including
composite orders.

## Licenses and citation

The paper (`c0_proof.tex` and `c0_proof.pdf`) is licensed under CC BY 4.0; see
`LICENSE-paper`. The Lean code and release tooling are licensed under the MIT
License; see `LICENSE-code`. `LICENSE` records the dual-license boundary.

Please cite the preferred paper citation in `CITATION.cff`. Version `1.0.0`
was released on 2026-07-18. A repository or Zenodo URL can be added to the CFF
metadata after the release record is assigned.
