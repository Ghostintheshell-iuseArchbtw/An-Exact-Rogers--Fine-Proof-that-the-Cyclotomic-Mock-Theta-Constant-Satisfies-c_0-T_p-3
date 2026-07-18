import MockTheta.Basic

/-!
# Products at an odd primitive root

All identities in this file are algebraic.  In particular, the complete
product is proved for every odd order; primality is not needed.
-/

noncomputable section

open scoped BigOperators

namespace MockTheta

open Finset Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {p : ℕ} {u : K}

/-- A power of an odd-order primitive root cannot equal `-1`. -/
theorem one_add_pow_ne_zero (hodd : Odd p) (hu : IsPrimitiveRoot u p) (j : ℕ) :
    1 + u ^ j ≠ 0 := by
  intro h
  have hj : u ^ j = -1 := by linear_combination h
  have hp := congrArg (fun z : K ↦ z ^ p) hj
  rw [← pow_mul, mul_comm, pow_mul, hu.pow_eq_one, one_pow, hodd.neg_one_pow] at hp
  have hne : (1 : K) ≠ -1 := by norm_num
  exact hne hp

private theorem reverse_prod_X_add_C (s : Finset ℕ) (a : ℕ → K) :
    Polynomial.reverse (∏ j ∈ s, (X + C (a j))) =
      ∏ j ∈ s, (1 + C (a j) * X) := by
  classical
  have reverse_one : Polynomial.reverse (1 : K[X]) = 1 := by
    rw [show (1 : K[X]) = C 1 by simp, Polynomial.reverse_C]
  have reverse_X : Polynomial.reverse (X : K[X]) = 1 := by
    rw [show (X : K[X]) = 1 * X by simp, Polynomial.reverse_mul_X, reverse_one]
  have reverse_linear (b : K) :
      Polynomial.reverse (X + C b) = 1 + C b * X := by
    rw [Polynomial.reverse_add_C, reverse_X]
    simp
  induction s using Finset.induction_on with
  | empty => simpa using reverse_one
  | @insert j s hjs ih =>
      simp only [Finset.prod_insert hjs, Polynomial.reverse_mul_of_domain, ih]
      rw [reverse_linear]

/-- The full denominator product at an odd primitive root. -/
theorem fullCycleProd (hodd : Odd p) (hp : 0 < p) (hu : IsPrimitiveRoot u p) :
    (∏ j ∈ Finset.range p, (1 + C (u ^ j) * X)) = (1 + X ^ p : K[X]) := by
  have hfactor := X_pow_sub_C_eq_prod hu hp (hodd.neg_one_pow : (-1 : K) ^ p = -1)
  have hfactor' :
      (X ^ p + 1 : K[X]) = ∏ j ∈ Finset.range p, (X + C (u ^ j)) := by
    simpa [sub_eq_add_neg] using hfactor
  have hrev := congrArg Polynomial.reverse hfactor'
  rw [reverse_prod_X_add_C] at hrev
  have hleft : Polynomial.reverse (X ^ p + 1 : K[X]) = 1 + X ^ p := by
    rw [show (1 : K[X]) = C 1 by simp, Polynomial.reverse_add_C]
    have hxpow : Polynomial.reverse (X ^ p : K[X]) = 1 := by
      rw [show (X ^ p : K[X]) = 1 * X ^ p by simp,
        Polynomial.reverse_mul_X_pow]
      rw [show (1 : K[X]) = C 1 by simp, Polynomial.reverse_C]
    rw [hxpow]
    simp
  rw [hleft] at hrev
  exact hrev.symm

/-- The cyclotomic defect is `1`; this remains true at odd composite orders. -/
theorem cyclotomicDefect (hodd : Odd p) (hp : 0 < p) (hu : IsPrimitiveRoot u p) :
    qPoch u (p - 1) = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hpoly := fullCycleProd (p := n + 1) (u := u) hodd (Nat.succ_pos n) hu
  have hev := congrArg (Polynomial.eval (1 : K)) hpoly
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow,
    one_pow] at hev
  rw [Finset.prod_range_succ'] at hev
  have hev' : qPoch u n * (2 : K) = 2 := by
    simpa [qPoch] using hev
  have htwo : (2 : K) ≠ 0 := by norm_num
  apply mul_right_cancel₀ htwo
  simpa using hev'

theorem qPoch_cycle (hodd : Odd p) (hp : 0 < p) (hu : IsPrimitiveRoot u p) :
    qPoch u p = 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hdef : qPoch u n = 1 := by
    simpa using cyclotomicDefect hodd (Nat.succ_pos n) hu
  rw [qPoch_succ, hdef, hu.pow_eq_one]
  ring

/-- Every denominator in `T` is nonzero before the end of an odd cycle. -/
theorem qPoch_ne_zero (hodd : Odd p) (hu : IsPrimitiveRoot u p) {n : ℕ}
    (_hn : n < p) : qPoch u n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simp only [Finset.mem_range] at hj
  exact one_add_pow_ne_zero hodd hu (j + 1)

end MockTheta
