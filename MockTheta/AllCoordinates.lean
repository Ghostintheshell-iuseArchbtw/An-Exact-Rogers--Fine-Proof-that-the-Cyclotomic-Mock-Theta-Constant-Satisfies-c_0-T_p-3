import MockTheta.PowerBasisCoordinates

/-!
# All cyclotomic power-basis coordinates

This extends the constant-coordinate construction to every basis index and
proves the redundant-to-genuine conversion uniformly.
-/

noncomputable section
open scoped BigOperators
namespace MockTheta
open Finset Polynomial

universe u v
variable {p : ℕ} {K : Type u} {L : Type v}
variable [NeZero p] [Field K] [Field L] [Algebra K L]
variable [IsCyclotomicExtension {p} K L]
variable {ζ : L}

/-- The `n`th power-basis coordinate, extended by zero outside the basis. -/
noncomputable def cCoeff (hζ : IsPrimitiveRoot ζ p) (n : ℕ) : L →ₗ[K] K :=
  if h : n < (hζ.powerBasis K).dim then
    (hζ.powerBasis K).basis.coord ⟨n, h⟩
  else 0

theorem cCoeff_apply_of_lt (hζ : IsPrimitiveRoot ζ p) {n : ℕ}
    (hn : n < (hζ.powerBasis K).dim) (x : L) :
    cCoeff (K := K) hζ n x =
      (hζ.powerBasis K).basis.repr x ⟨n, hn⟩ := by
  rw [cCoeff, dif_pos hn]
  rfl

theorem cCoeff_pow_of_lt (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hirr : Irreducible (cyclotomic p K)) {m n : ℕ}
    (hm : m < p - 1) (hn : n < p - 1) :
    cCoeff (K := K) hζ m (ζ ^ n) = if n = m then 1 else 0 := by
  let pb := hζ.powerBasis K
  have hdim : pb.dim = p - 1 := by
    letI : NeZero (p : K) := IsCyclotomicExtension.neZero' p K L
    rw [hζ.powerBasis_dim K,
      ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
      natDegree_cyclotomic, Nat.totient_prime hp]
  have hm' : m < pb.dim := by simpa [hdim] using hm
  let j : Fin pb.dim := ⟨n, by simpa [hdim] using hn⟩
  have hpow : ζ ^ n = pb.basis j := by
    rw [pb.basis_eq_pow]
    simp only [j]
    rw [hζ.powerBasis_gen K]
  rw [hpow, cCoeff_apply_of_lt hζ hm']
  simp only [j]
  rw [Module.Basis.repr_self_apply]
  congr 1
  apply propext
  constructor
  · intro h
    exact congrArg Fin.val h
  · intro h
    apply Fin.ext
    simpa using h

theorem cCoeff_pow_pred (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hirr : Irreducible (cyclotomic p K)) {m : ℕ} (hm : m < p - 1) :
    cCoeff (K := K) hζ m (ζ ^ (p - 1)) = -1 := by
  have hpow := hζ.pow_sub_one_eq hp.one_lt
  rw [Nat.pred_eq_sub_one] at hpow
  rw [hpow, map_neg, map_sum]
  have hmem : m ∈ range (p - 1) := by simpa using hm
  rw [sum_eq_add_sum_sdiff_singleton_of_mem hmem]
  · rw [cCoeff_pow_of_lt hζ hp hirr hm hm]
    simp only [if_pos, neg_add_rev]
    have hz :
        ∑ i ∈ range (p - 1) \ {m},
          cCoeff (K := K) hζ m (ζ ^ i) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hi' := mem_sdiff.mp hi
      rw [cCoeff_pow_of_lt hζ hp hirr hm (mem_range.mp hi'.1)]
      rw [if_neg (by simpa using hi'.2)]
    rw [hz]
    simp

/-- Conversion of a redundant length-`p` vector to any genuine power-basis
coordinate. -/
theorem cCoeff_redundant_sum (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hirr : Irreducible (cyclotomic p K)) (C : ℕ → K)
    {m : ℕ} (hm : m < p - 1) :
    cCoeff (K := K) hζ m
        (∑ n ∈ range p, algebraMap K L (C n) * ζ ^ n) =
      C m - C (p - 1) := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp.ne_zero
  have hprange : range p = range ((p - 1) + 1) := by congr 1 <;> omega
  rw [hprange, sum_range_succ, map_add, map_sum]
  have hmain :
      ∑ n ∈ range (p - 1),
          cCoeff (K := K) hζ m (algebraMap K L (C n) * ζ ^ n) = C m := by
    have hmmem : m ∈ range (p - 1) := by simpa using hm
    rw [sum_eq_add_sum_sdiff_singleton_of_mem hmmem]
    rw [← Algebra.smul_def, map_smul,
      cCoeff_pow_of_lt hζ hp hirr hm hm, if_pos rfl, smul_eq_mul,
      mul_one]
    have hz :
        ∑ n ∈ range (p - 1) \ {m},
          cCoeff (K := K) hζ m
            (algebraMap K L (C n) * ζ ^ n) = 0 := by
      apply sum_eq_zero
      intro n hn
      have hn' := mem_sdiff.mp hn
      rw [← Algebra.smul_def, map_smul,
        cCoeff_pow_of_lt hζ hp hirr hm (mem_range.mp hn'.1)]
      have hne : n ≠ m := by simpa using hn'.2
      rw [if_neg hne, smul_zero]
    rw [hz, add_zero]
  rw [hmain, ← Algebra.smul_def, map_smul,
    cCoeff_pow_pred hζ hp hirr hm, smul_eq_mul]
  ring

theorem cCoeff_zero_eq_c0 (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    (hirr : Irreducible (cyclotomic p K)) (x : L) :
    cCoeff (K := K) hζ 0 x = c0 (K := K) hζ x := by
  have hdim : (hζ.powerBasis K).dim = p - 1 := by
    letI : NeZero (p : K) := IsCyclotomicExtension.neZero' p K L
    rw [hζ.powerBasis_dim K,
      ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr,
      natDegree_cyclotomic, Nat.totient_prime hp]
  have hzero : 0 < (hζ.powerBasis K).dim := by
    rw [hdim]
    exact Nat.sub_pos_of_lt hp.one_lt
  rw [cCoeff_apply_of_lt hζ hzero]
  rfl

end MockTheta
