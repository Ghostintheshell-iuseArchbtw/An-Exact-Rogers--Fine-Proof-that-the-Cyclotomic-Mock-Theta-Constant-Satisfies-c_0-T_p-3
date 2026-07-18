import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.Tactic

/-!
# Cyclotomic mock-theta foundations

This file contains only the transparent definitions used throughout the
greenfield formalization.
-/

noncomputable section

open scoped BigOperators

namespace MockTheta

open Finset Polynomial

/-- The finite product `(-q;q)ₙ = ∏_{j=1}^n (1 + q^j)`. -/
def qPoch {K : Type*} [CommRing K] (q : K) (n : ℕ) : K :=
  ∏ j ∈ Finset.range n, (1 + q ^ (j + 1))

/-- The polynomial version of `(-q;q)ₙ`, with an extra variable in each factor. -/
def qPochPoly {K : Type*} [CommRing K] (q : K) (n : ℕ) : K[X] :=
  ∏ j ∈ Finset.range n, (1 + C (q ^ (j + 1)) * X)

/-- Euler's pentagonal exponent `n(3n+1)/2`. -/
def quadraticExp (n : ℕ) : ℕ :=
  n * (3 * n + 1) / 2

/-- The signed weight occurring in the finite weighted formula. -/
def weight (p n : ℕ) : ℤ :=
  (3 * (p : ℤ) - 1) / 2 - 3 * (n : ℤ)

/-- The original finite cyclotomic mock-theta sum. -/
def T {K : Type*} [Field K] (p : ℕ) (ζ : K) : K :=
  ∑ r ∈ Finset.range p, ζ ^ (r * r) / qPoch ζ r ^ 2

/-- The reverse-Fine finite sum. -/
def reverseFineSum {K : Type*} [CommRing K] (p : ℕ) (u : K) : K :=
  ∑ n ∈ Finset.range p, (-1 : K) ^ n * qPoch u n

/-- The polynomial appearing on the left of finite Rogers--Fine. -/
def rogersFineL {K : Type*} [CommRing K] (p : ℕ) (u : K) : K[X] :=
  ∑ n ∈ Finset.range p, C ((-1 : K) ^ n * qPoch u n) * X ^ n

/-- The tail product from index `n+1` through `p-1`. -/
def tailPoly {K : Type*} [CommRing K] (p n : ℕ) (u : K) : K[X] :=
  ∏ k ∈ Finset.range (p - (n + 1)), (1 + C (u ^ (n + 1 + k)) * X)

/-- The denominator-cleared right-hand summand in finite Rogers--Fine. -/
def rogersFineTerm {K : Type*} [CommRing K] (p : ℕ) (u : K) (n : ℕ) : K[X] :=
  C (qPoch u n * u ^ quadraticExp n) * X ^ (2 * n) *
    (1 - C (u ^ (2 * n + 1)) * X) * tailPoly p n u

/-- The complete denominator-cleared right side of finite Rogers--Fine. -/
def rogersFineR {K : Type*} [CommRing K] (p : ℕ) (u : K) : K[X] :=
  ∑ n ∈ Finset.range p, rogersFineTerm p u n

theorem qPoch_zero {K : Type*} [CommRing K] (q : K) : qPoch q 0 = 1 := by
  simp [qPoch]

theorem qPoch_succ {K : Type*} [CommRing K] (q : K) (n : ℕ) :
    qPoch q (n + 1) = qPoch q n * (1 + q ^ (n + 1)) := by
  simp [qPoch, Finset.prod_range_succ]

theorem two_mul_quadraticExp (n : ℕ) :
    2 * quadraticExp n = n * (3 * n + 1) := by
  apply Nat.two_mul_div_two_of_even
  rcases n.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact ⟨k * (3 * (2 * k) + 1), by ring⟩
  · exact ⟨(2 * k + 1) * (3 * k + 2), by ring⟩

@[simp] theorem quadraticExp_zero : quadraticExp 0 = 0 := by
  simp [quadraticExp]

theorem quadraticExp_succ (n : ℕ) :
    quadraticExp (n + 1) = quadraticExp n + 3 * n + 2 := by
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
  rw [two_mul_quadraticExp]
  simp only [mul_add]
  rw [two_mul_quadraticExp]
  ring

/-- Scale the polynomial variable by `q`. -/
def scalePoly {K : Type*} [CommRing K] (q : K) : K[X] →+* K[X] :=
  Polynomial.eval₂RingHom C (C q * X)

@[simp] theorem scalePoly_C {K : Type*} [CommRing K] (q a : K) :
    scalePoly q (C a) = C a := by
  simp [scalePoly]

@[simp] theorem scalePoly_X {K : Type*} [CommRing K] (q : K) :
    scalePoly q X = C q * X := by
  simp [scalePoly]

theorem scalePoly_C_mul_X_pow {K : Type*} [CommRing K] (q a : K) (n : ℕ) :
    scalePoly q (C a * X ^ n) = C (a * q ^ n) * X ^ n := by
  simp [scalePoly, mul_pow]
  ring

@[simp] theorem coeff_scalePoly {K : Type*} [CommRing K]
    (q : K) (f : K[X]) (n : ℕ) :
    (scalePoly q f).coeff n = q ^ n * f.coeff n := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]; ring
  | monomial m a =>
      unfold scalePoly
      change (eval₂ C (C q * X) (monomial m a)).coeff n = _
      rw [eval₂_monomial, mul_pow]
      have hC : (C q : K[X]) ^ m = C (q ^ m) := (map_pow C q m).symm
      rw [hC, ← mul_assoc, ← map_mul, C_mul_X_pow_eq_monomial]
      by_cases h : m = n
      · subst m
        simp
        ring
      · have h' : n ≠ m := Ne.symm h
        simp [coeff_monomial, h, h']

end MockTheta
