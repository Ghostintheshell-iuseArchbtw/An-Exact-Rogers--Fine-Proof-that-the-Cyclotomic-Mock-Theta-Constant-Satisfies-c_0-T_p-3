import MockTheta.PowerBasisCoordinates

/-!
# Constant coordinate of the reverse-Fine sum

This file rewrites the inverse quadratic exponents by their canonical
`ZMod p` representatives and applies the four-root calculation.  It proves
the constant-coordinate theorem for `reverseFineSum`; the separate Fine
collapse is the only bridge needed to transfer it to the original `T`.
-/

noncomputable section

open scoped BigOperators

namespace MockTheta

open Finset Polynomial

/-- Canonical redundant exponent representing `-quadraticExp n` modulo `p`. -/
def exponentResidue (p n : ℕ) : ℕ :=
  (-(quadraticExp n : ZMod p)).val

variable {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)

include hp7

theorem exponentResidue_lt (n : ℕ) : exponentResidue p n < p := by
  exact ZMod.val_lt _

variable {L : Type*} [Field L] {ζ : L}

theorem inv_pow_eq_pow_exponentResidue
    (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    (ζ⁻¹) ^ quadraticExp n = ζ ^ exponentResidue p n := by
  have hinv : ζ⁻¹ = ζ ^ (p - 1) := by
    field_simp [hζ.ne_zero]
    calc
      1 = ζ ^ p := hζ.pow_eq_one.symm
      _ = ζ ^ (p - 1 + 1) := by congr 1 <;> omega
      _ = ζ ^ (p - 1) * ζ := pow_succ ζ (p - 1)
      _ = ζ * ζ ^ (p - 1) := mul_comm _ _
  rw [hinv, ← pow_mul]
  apply (hζ.isOfFinOrder (by omega)).pow_eq_pow_iff_modEq.2
  rw [← hζ.eq_orderOf]
  apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
  unfold exponentResidue
  rw [ZMod.natCast_zmod_val]
  push_cast
  rw [cast_pred_order hp7]
  ring

variable [Algebra ℚ L] [IsCyclotomicExtension {p} ℚ L]

theorem c0_inv_quadratic (hζ : IsPrimitiveRoot ζ p) (n : ℕ) :
    c0 (K := ℚ) hζ ((ζ⁻¹) ^ quadraticExp n) =
      if (quadraticExp n : ZMod p) = 0 then 1
      else if (quadraticExp n : ZMod p) = 1 then -1 else 0 := by
  have hp : p.Prime := Fact.out
  rw [inv_pow_eq_pow_exponentResidue hp7 hζ n]
  by_cases h0 : (quadraticExp n : ZMod p) = 0
  · rw [if_pos h0]
    have hr : exponentResidue p n = 0 := by
      unfold exponentResidue
      rw [h0, neg_zero, ZMod.val_zero]
    rw [hr, pow_zero, c0_one hζ hp
      (cyclotomic.irreducible_rat hp.pos)]
  · rw [if_neg h0]
    by_cases h1 : (quadraticExp n : ZMod p) = 1
    · rw [if_pos h1]
      have hr : exponentResidue p n = p - 1 := by
        unfold exponentResidue
        rw [h1]
        apply Nat.ModEq.eq_of_lt_of_lt
          ((ZMod.natCast_eq_natCast_iff _ _ p).mp (by
            rw [ZMod.natCast_zmod_val, cast_pred_order hp7]))
          (ZMod.val_lt _) (by omega)
      rw [hr, c0_pow_pred hζ hp
        (cyclotomic.irreducible_rat hp.pos)]
    · rw [if_neg h1]
      apply c0_pow_ne_zero hζ hp
        (cyclotomic.irreducible_rat hp.pos)
      · have hrlt := exponentResidue_lt hp7 n
        have hrne : exponentResidue p n ≠ p - 1 := by
          intro hr
          have hc := congrArg (fun x : ℕ => (x : ZMod p)) hr
          unfold exponentResidue at hc
          rw [ZMod.natCast_zmod_val, cast_pred_order hp7] at hc
          have hneg : -(quadraticExp n : ZMod p) = -1 := hc
          apply h1
          linear_combination -hneg
        omega
      · intro hr
        apply h0
        have hc := congrArg (fun x : ℕ => (x : ZMod p)) hr
        unfold exponentResidue at hc
        rw [ZMod.natCast_zmod_val] at hc
        linear_combination -hc

/-- The principal constant-coordinate result after the finite Rogers--Fine
identity and formal differentiation.  It is stated for the reverse-Fine sum
so that the independent Fine-collapse bridge remains explicit. -/
theorem c0_reverseFine_eq_three (hζ : IsPrimitiveRoot ζ p) :
    c0 (K := ℚ) hζ (reverseFineSum p ζ⁻¹) = 3 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  letI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have hw := weighted_formula_reverse (K := L) hodd hp.pos hζ.inv
  rw [hw]
  have hpmap :
      algebraMap ℚ L ((p : ℚ)⁻¹) = (p : L)⁻¹ := by
    rw [map_inv₀]
    norm_num
  rw [← hpmap, ← Algebra.smul_def, map_smul, map_sum]
  have hweight (n : ℕ) :
      (((weight p n : ℤ) : L)) =
        algebraMap ℚ L (((weight p n : ℤ) : ℚ)) := by
    norm_num
  simp_rw [hweight, ← Algebra.smul_def, map_smul,
    c0_inv_quadratic hp7 hζ]
  simp only [smul_eq_mul]
  have hsum :
      (∑ n ∈ range p,
        (((weight p n : ℤ) : ℚ)) *
          (if (quadraticExp n : ZMod p) = 0 then 1
           else if (quadraticExp n : ZMod p) = 1 then -1 else 0)) =
        (∑ n ∈ (range p).filter
          (fun n => (quadraticExp n : ZMod p) = 0),
          (((weight p n : ℤ) : ℚ))) -
        (∑ n ∈ (range p).filter
          (fun n => (quadraticExp n : ZMod p) = 1),
          (((weight p n : ℤ) : ℚ))) := by
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h0 : (quadraticExp n : ZMod p) = 0
    · have h1 : (quadraticExp n : ZMod p) ≠ 1 := by
        rw [h0]
        exact zero_ne_one
      simp [h0, h1]
    · by_cases h1 : (quadraticExp n : ZMod p) = 1
      · simp [h1]
      · simp [h0, h1]
  rw [hsum]
  exact weighted_support_constant (K := ℚ) hp7

end MockTheta
