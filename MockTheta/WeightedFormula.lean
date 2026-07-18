import MockTheta.RogersFineFinite

/-!
# Formal differentiation and the weighted Rogers--Fine formula

Everything in this file is finite algebra.  The logarithmic derivatives below
are ordinary finite sums and `finiteRogersFine` is differentiated as an
identity in `Polynomial K`.
-/

noncomputable section

open scoped BigOperators

namespace MockTheta

open Finset Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {p n j : ℕ} {u : K}

/-- A summand in the logarithmic derivative of the cyclotomic product. -/
def rootFrac (u : K) (j : ℕ) : K := u ^ j / (1 + u ^ j)

/-- Logarithmic derivative of the tail from `n+1` through `p-1`. -/
def tailLog (p n : ℕ) (u : K) : K :=
  ∑ k ∈ Finset.range (p - (n + 1)), rootFrac u (n + 1 + k)

/-- Logarithmic derivative over one full root-of-unity cycle. -/
def fullLog (p : ℕ) (u : K) : K :=
  ∑ j ∈ Finset.range p, rootFrac u j

private theorem eval_derivative_prod_linear (s : Finset ℕ) (a : ℕ → K)
    (ha : ∀ i ∈ s, 1 + a i ≠ 0) :
    eval 1 (derivative (∏ i ∈ s, (1 + C (a i) * X))) =
      (∏ i ∈ s, (1 + a i)) * ∑ i ∈ s, a i / (1 + a i) := by
  rw [derivative_prod_finset, eval_finsetSum]
  simp only [eval_mul, derivative_add, derivative_one, derivative_mul,
    derivative_C, derivative_X, zero_add, zero_mul, mul_one,
    eval_prod, eval_add, eval_one, eval_C, eval_X]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hprod := Finset.prod_erase_mul s (fun j => 1 + a j) hi
  rw [← hprod]
  field_simp [ha i hi]

theorem qPoch_mul_eval_tail (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) (hn : n < p) :
    qPoch u n * eval 1 (tailPoly p n u) = 1 := by
  have hlen : p - 1 = n + (p - (n + 1)) := by omega
  have hdef := cyclotomicDefect hodd hp hu
  unfold qPoch at hdef ⊢
  unfold tailPoly
  simp only [eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X, mul_one]
  rw [hlen, Finset.prod_range_add] at hdef
  convert hdef using 1 <;> ring

theorem fullLog_eq_half_order (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    fullLog p u = (p : K) / 2 := by
  have hlog := eval_derivative_prod_linear (K := K) (Finset.range p) (fun j => u ^ j)
    (fun j _ => one_add_pow_ne_zero hodd hu j)
  have hpoly := fullCycleProd (p := p) (u := u) hodd hp hu
  have heval := congrArg (Polynomial.eval (1 : K)) hpoly
  simp only [eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X,
    eval_pow, one_pow] at heval
  norm_num at heval
  have hprod : (∏ i ∈ Finset.range p, (1 + u ^ i)) = (2 : K) := by
    simpa only [mul_one] using heval
  rw [hpoly, hprod] at hlog
  simp only [derivative_add, derivative_one, derivative_X_pow, eval_add,
    eval_zero, eval_mul, eval_C, eval_pow, eval_X, one_pow, zero_add, mul_one] at hlog
  change (p : K) = 2 * fullLog p u at hlog
  apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).2
  simpa [mul_comm] using hlog.symm

theorem rootFrac_complement (hodd : Odd p) (hu : IsPrimitiveRoot u p)
    (hj : j ≤ p) :
    rootFrac u (p - j) + rootFrac u j = 1 := by
  have hab : u ^ (p - j) * u ^ j = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hj, hu.pow_eq_one]
  unfold rootFrac
  field_simp [one_add_pow_ne_zero hodd hu]
  linear_combination hab

private theorem tailLog_reflect (hodd : Odd p) (hu : IsPrimitiveRoot u p)
    (hn : n < p) :
    tailLog p n u =
      (p - 1 - n : ℕ) -
        ∑ k ∈ Finset.range (p - 1 - n), rootFrac u (k + 1) := by
  let m := p - 1 - n
  have hlen : p - (n + 1) = m := by dsimp [m]; omega
  have hreflect : tailLog p n u =
      ∑ k ∈ Finset.range m, rootFrac u (p - (k + 1)) := by
    unfold tailLog
    rw [hlen, ← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    congr 2
    dsimp [m] at hk ⊢
    simp only [Finset.mem_range] at hk
    omega
  rw [hreflect]
  calc
    (∑ k ∈ Finset.range m, rootFrac u (p - (k + 1))) =
        ∑ k ∈ Finset.range m, (1 - rootFrac u (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkp : k + 1 ≤ p := by
        dsimp [m] at hk
        simp only [Finset.mem_range] at hk
        omega
      have hc := rootFrac_complement (u := u) hodd hu hkp
      linear_combination hc
    _ = (m : K) - ∑ k ∈ Finset.range m, rootFrac u (k + 1) := by
      simp [Finset.sum_sub_distrib]

theorem tailLog_symmetry (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) (hn : n < p) :
    tailLog p n u - tailLog p (p - 1 - n) u =
      ((p : K) - 1) / 2 - (n : K) := by
  let m := p - 1 - n
  have hm : m + n + 1 = p := by dsimp [m]; omega
  have hreflect := tailLog_reflect (K := K) (u := u) hodd hu hn
  change tailLog p n u =
    (m : K) - ∑ k ∈ Finset.range m, rootFrac u (k + 1) at hreflect
  have hdecomp : fullLog p u =
      (∑ k ∈ Finset.range m, rootFrac u (k + 1)) + rootFrac u 0 +
        tailLog p m u := by
    unfold fullLog tailLog
    have hpdecomp : p = (m + 1) + (p - (m + 1)) := by
      dsimp [m]
      omega
    conv_lhs => rw [hpdecomp, Finset.sum_range_add, Finset.sum_range_succ']
  have hfull := fullLog_eq_half_order (K := K) hodd hp hu
  have hf0 : rootFrac u 0 = (1 : K) / 2 := by
    simp [rootFrac]
    norm_num
  have hmK : (m : K) + (n : K) + 1 = (p : K) := by exact_mod_cast hm
  rw [hf0] at hdecomp
  change tailLog p n u - tailLog p m u = _
  linear_combination hreflect + hdecomp - hfull + hmK

theorem qPoch_mul_eval_derivative_tail (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) (hn : n < p) :
    qPoch u n * eval 1 (derivative (tailPoly p n u)) = tailLog p n u := by
  have hlog := eval_derivative_prod_linear (K := K)
    (Finset.range (p - (n + 1))) (fun k => u ^ (n + 1 + k))
    (fun k _ => one_add_pow_ne_zero hodd hu (n + 1 + k))
  have htail : eval 1 (derivative (tailPoly p n u)) =
      eval 1 (tailPoly p n u) * tailLog p n u := by
    unfold tailPoly tailLog
    simpa only [rootFrac, eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X,
      mul_one] using hlog
  rw [htail, ← mul_assoc, qPoch_mul_eval_tail hodd hp hu hn, one_mul]

theorem quadraticExp_reflection_pow (hodd : Odd p) (hu : IsPrimitiveRoot u p)
    (hn : n < p) :
    u ^ (quadraticExp n + 2 * n + 1) =
      u ^ quadraticExp (p - 1 - n) := by
  let m := p - 1 - n
  have hm : m + n + 1 = p := by dsimp [m]; omega
  have hdouble :
      2 * (quadraticExp n + 2 * n + 1) ≡ 2 * quadraticExp m [MOD p] := by
    rw [Nat.modEq_iff_dvd]
    refine ⟨(3 * (p : ℤ) - 6 * (n : ℤ) - 5), ?_⟩
    push_cast
    have hAn : (2 : ℤ) * (quadraticExp n : ℤ) =
        (n : ℤ) * (3 * (n : ℤ) + 1) := by
      exact_mod_cast two_mul_quadraticExp n
    have hAm : (2 : ℤ) * (quadraticExp m : ℤ) =
        (m : ℤ) * (3 * (m : ℤ) + 1) := by
      exact_mod_cast two_mul_quadraticExp m
    have hmZ : (m : ℤ) + (n : ℤ) + 1 = (p : ℤ) := by exact_mod_cast hm
    linear_combination hAm - hAn +
      (3 * (m : ℤ) - 3 * (n : ℤ) - 2 + 3 * (p : ℤ)) * hmZ
  have hmod : quadraticExp n + 2 * n + 1 ≡ quadraticExp m [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime hodd.coprime_two_right hdouble
  exact pow_eq_pow_of_modEq hmod hu.pow_eq_one

private theorem eval_derivative_rogersFineTerm (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) (hn : n < p) :
    eval 1 (derivative (rogersFineTerm p u n)) =
      u ^ quadraticExp n *
        ((2 * n : ℕ) * (1 - u ^ (2 * n + 1)) - u ^ (2 * n + 1) +
          (1 - u ^ (2 * n + 1)) * tailLog p n u) := by
  have htail := qPoch_mul_eval_tail (K := K) hodd hp hu hn
  have htailD := qPoch_mul_eval_derivative_tail (K := K) hodd hp hu hn
  unfold rogersFineTerm
  simp only [derivative_mul, derivative_C, derivative_X_pow, derivative_sub,
    derivative_one, derivative_X, zero_sub, eval_add, eval_zero, eval_mul, eval_C,
    eval_pow, eval_X, one_pow, eval_sub, eval_one, eval_neg, mul_one]
  push_cast
  linear_combination (u ^ quadraticExp n * ((2 * n : K) *
      (1 - u ^ (2 * n + 1)) - u ^ (2 * n + 1))) * htail +
    (u ^ quadraticExp n * (1 - u ^ (2 * n + 1))) * htailD

@[simp] theorem eval_rogersFineL_one :
    eval 1 (rogersFineL p u) = reverseFineSum p u := by
  unfold rogersFineL reverseFineSum
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n hn
  simp

private theorem derivative_finiteRogersFine (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    -(p : K) * reverseFineSum p u =
      ∑ n ∈ Finset.range p,
        u ^ quadraticExp n *
          ((2 * n : ℕ) * (1 - u ^ (2 * n + 1)) - u ^ (2 * n + 1) +
            (1 - u ^ (2 * n + 1)) * tailLog p n u) := by
  have hfrf := finiteRogersFine (p := p) (u := u) hodd hp hu
  have hderiv := congrArg (fun f : K[X] => eval 1 (derivative f)) hfrf
  rw [show eval 1 (derivative ((1 - X ^ p) * rogersFineL p u)) =
      -(p : K) * reverseFineSum p u by
    rw [derivative_mul]
    simp only [derivative_sub, derivative_one, derivative_X_pow, zero_sub,
      eval_add, eval_mul, eval_neg, eval_C, eval_pow, eval_X, one_pow,
      eval_sub, eval_one, sub_self, zero_mul, add_zero, eval_rogersFineL_one]
    ring] at hderiv
  unfold rogersFineR at hderiv
  rw [derivative_sum, eval_finsetSum] at hderiv
  rw [hderiv]
  apply Finset.sum_congr rfl
  intro n hn
  exact eval_derivative_rogersFineTerm hodd hp hu (by simpa using hn)

private theorem derivative_sum_simplify (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    (∑ n ∈ Finset.range p,
        u ^ quadraticExp n *
          ((2 * n : ℕ) * (1 - u ^ (2 * n + 1)) - u ^ (2 * n + 1) +
            (1 - u ^ (2 * n + 1)) * tailLog p n u)) =
      ∑ n ∈ Finset.range p,
        u ^ quadraticExp n *
          (3 * (n : K) - (3 * (p : K) - 1) / 2) := by
  let first : ℕ → K := fun n =>
    u ^ quadraticExp n * ((2 * n : ℕ) + tailLog p n u)
  let second : ℕ → K := fun n =>
    u ^ (quadraticExp n + 2 * n + 1) *
      ((2 * n : ℕ) + tailLog p n u + 1)
  have hsplit :
      (∑ n ∈ Finset.range p,
        u ^ quadraticExp n *
          ((2 * n : ℕ) * (1 - u ^ (2 * n + 1)) - u ^ (2 * n + 1) +
            (1 - u ^ (2 * n + 1)) * tailLog p n u)) =
        (∑ n ∈ Finset.range p, first n) -
          ∑ n ∈ Finset.range p, second n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [first, second]
    rw [pow_add]
    push_cast
    ring
  rw [hsplit]
  have hreflect :
      (∑ n ∈ Finset.range p, second n) =
        ∑ n ∈ Finset.range p,
          u ^ quadraticExp n *
            ((2 * (p - 1 - n) : ℕ) + tailLog p (p - 1 - n) u + 1) := by
    calc
      (∑ n ∈ Finset.range p, second n) =
          ∑ n ∈ Finset.range p, second (p - 1 - n) :=
        (Finset.sum_range_reflect second p).symm
      _ = ∑ n ∈ Finset.range p,
          u ^ quadraticExp n *
            ((2 * (p - 1 - n) : ℕ) + tailLog p (p - 1 - n) u + 1) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [Finset.mem_range] at hn
        have hm : p - 1 - n < p := by omega
        have he := quadraticExp_reflection_pow (u := u) hodd hu hm
        have hcomp : p - 1 - (p - 1 - n) = n := by omega
        dsimp only [second]
        rw [he, hcomp]
  rw [hreflect, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_range] at hn
  have hs := tailLog_symmetry (K := K) (u := u) hodd hp hu hn
  let m := p - 1 - n
  have hm : m + n + 1 = p := by dsimp [m]; omega
  have hmK : (m : K) + (n : K) + 1 = (p : K) := by exact_mod_cast hm
  change first n -
      u ^ quadraticExp n * ((2 * m : ℕ) + tailLog p m u + 1) = _
  dsimp only [first]
  change tailLog p n u - tailLog p m u = _ at hs
  push_cast
  linear_combination (u ^ quadraticExp n) * hs -
    (2 * u ^ quadraticExp n) * hmK

theorem cast_weight (hodd : Odd p) (n : ℕ) :
    (((weight p n : ℤ) : K)) =
      (3 * (p : K) - 1) / 2 - 3 * (n : K) := by
  rcases hodd with ⟨k, rfl⟩
  have hw : weight (2 * k + 1) n =
      (3 * (k : ℤ) + 1 - 3 * (n : ℤ)) := by
    unfold weight
    norm_num
    omega
  rw [hw]
  push_cast
  ring

/-- Weighted Rogers--Fine formula for the reverse-Fine finite sum. -/
theorem weighted_formula_reverse (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    reverseFineSum p u =
      (p : K)⁻¹ *
        ∑ n ∈ Finset.range p,
          (((weight p n : ℤ) : K)) * u ^ quadraticExp n := by
  have hd := derivative_finiteRogersFine (K := K) hodd hp hu
  have hs := derivative_sum_simplify (K := K) hodd hp hu
  rw [hs] at hd
  have hsum :
      (p : K) * reverseFineSum p u =
        ∑ n ∈ Finset.range p,
          (((weight p n : ℤ) : K)) * u ^ quadraticExp n := by
    calc
      (p : K) * reverseFineSum p u =
          -∑ n ∈ Finset.range p,
            u ^ quadraticExp n *
              (3 * (n : K) - (3 * (p : K) - 1) / 2) := by
        linear_combination -hd
      _ = ∑ n ∈ Finset.range p,
          (((weight p n : ℤ) : K)) * u ^ quadraticExp n := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        rw [cast_weight (K := K) hodd n]
        ring
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne'
  rw [← hsum]
  field_simp

end MockTheta
