import MockTheta.WeightedFormula

/-!
# Quadratic congruences for the constant coordinate

This file solves, with canonical natural representatives, the two congruences
that support the redundant coefficients of exponents `0` and `-1`.
-/

noncomputable section

open scoped BigOperators

namespace MockTheta

open Finset

/-- The canonical representative of the nonzero solution of
`n * (3 * n + 1) = 0` in `ZMod p`. -/
def specialRoot (p : ℕ) [Fact p.Prime] : ℕ :=
  (-((3 : ZMod p)⁻¹)).val

variable {p : ℕ}

theorem zmod_quadraticExp_double (n : ℕ) :
    (2 : ZMod p) * (quadraticExp n : ZMod p) =
      (n : ZMod p) * (3 * (n : ZMod p) + 1) := by
  have h := congrArg (fun x : ℕ => (x : ZMod p)) (two_mul_quadraticExp n)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using h

section Prime

variable [Fact p.Prime] (hp7 : 7 ≤ p)

include hp7

private theorem three_ne_zero : (3 : ZMod p) ≠ 0 := by
  change ((3 : ℕ) : ZMod p) ≠ 0
  intro h
  have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
  have := Nat.le_of_dvd (by omega : 0 < 3) hd
  omega

private theorem two_ne_zero : (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  intro h
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
  have := Nat.le_of_dvd (by omega : 0 < 2) hd
  omega

theorem specialRoot_lt : specialRoot p < p := by
  apply ZMod.val_lt

theorem specialRoot_cast :
    (specialRoot p : ZMod p) = -((3 : ZMod p)⁻¹) := by
  exact ZMod.natCast_zmod_val _

theorem specialRoot_equation :
    (3 : ZMod p) * (specialRoot p : ZMod p) + 1 = 0 := by
  rw [specialRoot_cast hp7]
  have h3 := three_ne_zero hp7
  rw [mul_neg, mul_inv_cancel₀ h3]
  ring

theorem specialRoot_succ_lt : specialRoot p + 1 < p := by
  have ha := specialRoot_lt hp7
  by_contra h
  have hae : specialRoot p = p - 1 := by omega
  have heq := specialRoot_equation hp7
  rw [hae] at heq
  have hpcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
    have hppos : 0 < p := by omega
    have hc := congrArg (fun x : ℕ => (x : ZMod p))
      (show p - 1 + 1 = p by omega)
    push_cast at hc
    rw [ZMod.natCast_self] at hc
    linear_combination hc
  rw [hpcast] at heq
  have h2 := two_ne_zero hp7
  apply h2
  linear_combination -heq

private theorem natCast_eq_of_lt {a b : ℕ} (ha : a < p) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  apply Nat.ModEq.eq_of_lt_of_lt _ ha hb
  exact (ZMod.natCast_eq_natCast_iff a b p).mp h

theorem quadraticExp_eq_zero_iff {n : ℕ} (hn : n < p) :
    (quadraticExp n : ZMod p) = 0 ↔
      n = 0 ∨ n = specialRoot p := by
  constructor
  · intro hA
    have hd := zmod_quadraticExp_double (p := p) n
    rw [hA, mul_zero] at hd
    rcases mul_eq_zero.mp hd.symm with hn0 | hlin
    · left
      rw [ZMod.natCast_eq_zero_iff] at hn0
      exact Nat.eq_zero_of_dvd_of_lt hn0 hn
    · right
      have h3 := three_ne_zero hp7
      have hcast : (n : ZMod p) = -((3 : ZMod p)⁻¹) := by
        apply mul_left_cancel₀ h3
        field_simp [h3] at hlin ⊢
        linear_combination hlin
      rw [← specialRoot_cast hp7] at hcast
      exact natCast_eq_of_lt hp7 hn (specialRoot_lt hp7) hcast
  · rintro (rfl | rfl)
    · simp [quadraticExp]
    · have hd := zmod_quadraticExp_double (p := p) (specialRoot p)
      rw [specialRoot_equation hp7, mul_zero] at hd
      exact (mul_eq_zero.mp hd).resolve_left (two_ne_zero hp7)

theorem cast_pred_order : ((p - 1 : ℕ) : ZMod p) = -1 := by
  have hppos : 0 < p := by omega
  have hc := congrArg (fun x : ℕ => (x : ZMod p))
    (show p - 1 + 1 = p by omega)
  push_cast at hc
  rw [ZMod.natCast_self] at hc
  linear_combination hc

theorem quadraticExp_eq_one_iff {n : ℕ} (hn : n < p) :
    (quadraticExp n : ZMod p) = 1 ↔
      n = p - 1 ∨ n = specialRoot p + 1 := by
  constructor
  · intro hA
    have hd := zmod_quadraticExp_double (p := p) n
    rw [hA, mul_one] at hd
    have hfac :
        (3 * (n : ZMod p) - 2) * ((n : ZMod p) + 1) = 0 := by
      linear_combination -hd
    rcases mul_eq_zero.mp hfac with hfirst | hsecond
    · right
      have h3 := three_ne_zero hp7
      have hcast : (n : ZMod p) = (specialRoot p + 1 : ℕ) := by
        apply mul_left_cancel₀ h3
        push_cast
        have ha := specialRoot_equation hp7
        linear_combination hfirst - ha
      exact natCast_eq_of_lt hp7 hn (specialRoot_succ_lt hp7) hcast
    · left
      have hcast : (n : ZMod p) = (p - 1 : ℕ) := by
        rw [cast_pred_order hp7]
        linear_combination hsecond
      exact natCast_eq_of_lt hp7 hn (by omega) hcast
  · rintro (rfl | rfl)
    · have hd := zmod_quadraticExp_double (p := p) (p - 1)
      rw [cast_pred_order hp7] at hd
      have h2 := two_ne_zero hp7
      apply mul_left_cancel₀ h2
      rw [hd]
      ring
    · have hd := zmod_quadraticExp_double (p := p) (specialRoot p + 1)
      have ha := specialRoot_equation hp7
      push_cast at hd
      have h2 := two_ne_zero hp7
      apply mul_left_cancel₀ h2
      rw [hd]
      linear_combination ((specialRoot p : ZMod p) + 2) * ha

private theorem five_ne_zero : (5 : ZMod p) ≠ 0 := by
  change ((5 : ℕ) : ZMod p) ≠ 0
  intro h
  have hd : p ∣ 5 := (ZMod.natCast_eq_zero_iff 5 p).mp h
  have := Nat.le_of_dvd (by omega : 0 < 5) hd
  omega

theorem specialRoot_ne_zero : specialRoot p ≠ 0 := by
  intro ha
  have he := specialRoot_equation hp7
  rw [ha] at he
  norm_num at he

theorem specialRoot_succ_ne_pred : specialRoot p + 1 ≠ p - 1 := by
  intro h
  have hc := congrArg (fun x : ℕ => (x : ZMod p)) h
  push_cast at hc
  rw [cast_pred_order hp7] at hc
  have ha := specialRoot_equation hp7
  have h5 : (5 : ZMod p) = 0 := by
    linear_combination 3 * hc - ha
  exact five_ne_zero hp7 h5

theorem zeroSupport :
    (range p).filter (fun n => (quadraticExp n : ZMod p) = 0) =
      {0, specialRoot p} := by
  ext n
  simp only [mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hn, hA⟩
    exact (quadraticExp_eq_zero_iff hp7 hn).mp hA
  · intro hn
    have hlt : n < p := by
      rcases hn with rfl | rfl
      · omega
      · exact specialRoot_lt hp7
    exact ⟨hlt, (quadraticExp_eq_zero_iff hp7 hlt).mpr hn⟩

theorem oneSupport :
    (range p).filter (fun n => (quadraticExp n : ZMod p) = 1) =
      {p - 1, specialRoot p + 1} := by
  ext n
  simp only [mem_filter, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hn, hA⟩
    exact (quadraticExp_eq_one_iff hp7 hn).mp hA
  · intro hn
    have hlt : n < p := by
      rcases hn with rfl | rfl
      · omega
      · exact specialRoot_succ_lt hp7
    exact ⟨hlt, (quadraticExp_eq_one_iff hp7 hlt).mpr hn⟩

theorem weight_zero_sub_pred :
    weight p 0 - weight p (p - 1) = 3 * ((p : ℤ) - 1) := by
  have hp : 1 ≤ p := by omega
  unfold weight
  rw [Int.ofNat_sub hp]
  push_cast
  ring

theorem weight_succ_difference (a : ℕ) :
    weight p a - weight p (a + 1) = 3 := by
  unfold weight
  push_cast
  ring

variable {K : Type*} [Field K] [CharZero K]

/-- The redundant coefficients at exponents `0` and `-1` contribute exactly
`3` to the constant power-basis coordinate. -/
theorem weighted_support_constant :
    (p : K)⁻¹ *
      ((∑ n ∈ (range p).filter
          (fun n => (quadraticExp n : ZMod p) = 0),
          (((weight p n : ℤ) : K))) -
        (∑ n ∈ (range p).filter
          (fun n => (quadraticExp n : ZMod p) = 1),
          (((weight p n : ℤ) : K)))) = 3 := by
  rw [zeroSupport hp7, oneSupport hp7]
  rw [sum_insert (by simpa using (specialRoot_ne_zero hp7).symm), sum_singleton]
  rw [sum_insert (by simpa using (specialRoot_succ_ne_pred hp7).symm), sum_singleton]
  have h0 := congrArg (fun z : ℤ => (z : K)) (weight_zero_sub_pred hp7)
  have ha := congrArg (fun z : ℤ => (z : K))
    (weight_succ_difference hp7 (specialRoot p))
  push_cast at h0 ha
  have hpK : (p : K) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 by omega)
  field_simp
  linear_combination h0 + ha

end Prime

end MockTheta
