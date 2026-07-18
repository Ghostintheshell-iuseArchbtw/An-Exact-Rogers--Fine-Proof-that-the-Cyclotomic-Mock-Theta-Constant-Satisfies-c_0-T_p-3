import MockTheta.CyclotomicProducts

/-!
# Finite Rogers--Fine polynomial identity

The proof uses a polynomial q-difference equation.  No infinite series or
analytic continuation is involved.
-/

noncomputable section

open scoped BigOperators

namespace MockTheta

open Finset Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {p : ℕ} {u : K}

theorem tailPoly_succ {n : ℕ} (hn : n + 1 < p) :
    tailPoly p n u = (1 + C (u ^ (n + 1)) * X) * tailPoly p (n + 1) u := by
  unfold tailPoly
  have hlen : p - (n + 1) = (p - (n + 2)) + 1 := by omega
  rw [hlen, Finset.prod_range_succ']
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  congr 3
  congr 1
  omega

theorem scalePoly_tailPoly {n : ℕ} (hn : n + 1 < p) (hu : IsPrimitiveRoot u p) :
    scalePoly u (tailPoly p n u) = (1 + X) * tailPoly p (n + 1) u := by
  unfold tailPoly
  simp only [map_prod, map_add, map_one, map_mul, scalePoly_C, scalePoly_X,
    ← map_pow, map_mul]
  have hlen : p - (n + 1) = (p - (n + 2)) + 1 := by omega
  rw [hlen, Finset.prod_range_succ]
  have hlast : (n + 1 + (p - (n + 2))) + 1 = p := by omega
  have hlastFactor :
      1 + C (u ^ (n + 1 + (p - (n + 2)))) * (C u * X) = 1 + X := by
    rw [← mul_assoc, ← map_mul, ← pow_succ, hlast, hu.pow_eq_one]
    simp
  rw [hlastFactor, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [← mul_assoc, ← map_mul, ← pow_succ]
  congr 3
  congr 1
  omega

@[simp] theorem tailPoly_at_last (hp : 0 < p) : tailPoly p (p - 1) u = 1 := by
  simp [tailPoly, Nat.sub_add_cancel hp, hp]

@[simp] theorem tailPoly_at_order : tailPoly p p u = 1 := by
  simp [tailPoly]

theorem one_add_X_mul_tail_zero (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    (1 + X) * tailPoly p 0 u = 1 + X ^ p := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hfull := fullCycleProd (p := n + 1) (u := u) hodd (Nat.succ_pos n) hu
  rw [Finset.prod_range_succ'] at hfull
  simpa [tailPoly, add_comm, pow_zero, mul_comm] using hfull

private def lTerm (u : K) (n : ℕ) : K[X] :=
  C ((-1 : K) ^ n * qPoch u n) * X ^ n

private theorem lTerm_succ (u : K) (n : ℕ) :
    lTerm u (n + 1) =
      -(C ((-1 : K) ^ n * qPoch u n * (1 + u ^ (n + 1))) * X ^ (n + 1)) := by
  unfold lTerm
  rw [qPoch_succ]
  simp only [pow_succ, map_mul, map_add, map_one, map_neg]
  ring

theorem rogersFineL_qdiff (hodd : Odd p) (hp : 0 < p) (hu : IsPrimitiveRoot u p) :
    (1 + X) * rogersFineL p u + C u * X * scalePoly u (rogersFineL p u) =
      1 + 2 * X ^ p := by
  let f : ℕ → K[X] := lTerm u
  have hshift (n : ℕ) :
      X * f n + C u * X * scalePoly u (f n) = -f (n + 1) := by
    dsimp only [f]
    rw [lTerm_succ]
    unfold lTerm
    rw [scalePoly_C_mul_X_pow]
    simp only [map_mul, map_add, map_one]
    simp only [pow_succ, map_mul]
    ring
  have hexpand :
      (1 + X) * rogersFineL p u + C u * X * scalePoly u (rogersFineL p u) =
        (∑ n ∈ Finset.range p, f n) +
          ∑ n ∈ Finset.range p, (X * f n + C u * X * scalePoly u (f n)) := by
    simp only [rogersFineL, f, lTerm, add_mul, one_mul, Finset.mul_sum,
      map_sum, Finset.sum_add_distrib]
    ring
  rw [hexpand]
  simp_rw [hshift]
  rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, ← Finset.sum_sub_distrib,
    Finset.sum_range_sub']
  simp only [f, lTerm, qPoch_zero, pow_zero, mul_one, C_1]
  rw [qPoch_cycle hodd hp hu, hodd.neg_one_pow]
  norm_num
  simp [Polynomial.C_ofNat]

private def gTerm (p : ℕ) (u : K) (n : ℕ) : K[X] :=
  C (qPoch u n * u ^ quadraticExp n) * X ^ (2 * n) * (1 + X) * tailPoly p n u

private theorem rogersFineTerm_qdiff {n : ℕ} (hn : n + 1 < p)
    (hu : IsPrimitiveRoot u p) :
    (1 + X) * rogersFineTerm p u n +
        C u * X * scalePoly u (rogersFineTerm p u n) =
      gTerm p u n - gTerm p u (n + 1) := by
  unfold rogersFineTerm gTerm
  simp only [map_mul]
  rw [scalePoly_tailPoly hn hu, tailPoly_succ hn, qPoch_succ, quadraticExp_succ]
  simp only [map_mul, map_sub, map_one, scalePoly_C, scalePoly_X, map_pow,
    mul_pow, map_add, pow_add, pow_succ]
  ring

private theorem quadraticExp_order_pow (hodd : Odd p) (hu : IsPrimitiveRoot u p) :
    u ^ quadraticExp p = 1 := by
  rcases hodd with ⟨k, hk⟩
  have hA : quadraticExp p = p * (3 * k + 2) := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
    rw [two_mul_quadraticExp]
    subst p
    ring
  rw [hA, pow_mul, hu.pow_eq_one, one_pow]

private theorem rogersFineTerm_qdiff_last (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    (1 + X) * rogersFineTerm p u (p - 1) +
        C u * X * scalePoly u (rogersFineTerm p u (p - 1)) =
      gTerm p u (p - 1) - 2 * X ^ (2 * p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hdef : qPoch u n = 1 := by
    simpa using cyclotomicDefect hodd (Nat.succ_pos n) hu
  have hAp : u ^ quadraticExp (n + 1) = 1 := quadraticExp_order_pow hodd hu
  simp only [Nat.succ_sub_one]
  have htail : tailPoly (n + 1) n u = 1 := by
    simpa using tailPoly_at_last (p := n + 1) (u := u) (Nat.succ_pos n)
  unfold rogersFineTerm gTerm
  simp only [map_mul]
  rw [htail, hdef]
  simp only [mul_one, map_mul, map_sub, map_one, scalePoly_C, scalePoly_X,
    map_pow, mul_pow, map_add, pow_add, pow_succ]
  have hpow := hu.pow_eq_one
  push_cast
  ring_nf at ⊢
  have hE1 : u ^ (quadraticExp n + 2 * n + 1) = 1 := by
    have hexp : (quadraticExp n + 2 * n + 1) + (n + 1) =
        quadraticExp (n + 1) := by
      rw [quadraticExp_succ]
      ring
    calc
      u ^ (quadraticExp n + 2 * n + 1) =
          u ^ (quadraticExp n + 2 * n + 1) * u ^ (n + 1) := by
            rw [hpow, mul_one]
      _ = u ^ ((quadraticExp n + 2 * n + 1) + (n + 1)) :=
        (pow_add u (quadraticExp n + 2 * n + 1) (n + 1)).symm
      _ = u ^ quadraticExp (n + 1) := by rw [hexp]
      _ = 1 := hAp
  have hE2 : u ^ (quadraticExp n + 4 * n + 3) = 1 := by
    have hexp : quadraticExp n + 4 * n + 3 =
        (quadraticExp n + 2 * n + 1) + 2 * (n + 1) := by ring
    calc
      u ^ (quadraticExp n + 4 * n + 3) =
          u ^ ((quadraticExp n + 2 * n + 1) + 2 * (n + 1)) := by rw [hexp]
      _ = u ^ (quadraticExp n + 2 * n + 1) * u ^ (2 * (n + 1)) :=
        pow_add u (quadraticExp n + 2 * n + 1) (2 * (n + 1))
      _ = u ^ (quadraticExp n + 2 * n + 1) * (u ^ (n + 1)) ^ 2 := by
        congr 1
        rw [show 2 * (n + 1) = (n + 1) * 2 by ring, pow_mul]
      _ = 1 := by rw [hE1, hpow, one_pow, mul_one]
  have hs1 : u * u ^ (n * 2) * u ^ quadraticExp n = 1 := by
    calc
      u * u ^ (n * 2) * u ^ quadraticExp n =
          u ^ 1 * u ^ (n * 2) * u ^ quadraticExp n := by rw [pow_one]
      _ = u ^ (1 + n * 2) * u ^ quadraticExp n := by
        rw [pow_add]
      _ = u ^ (1 + n * 2 + quadraticExp n) :=
        (pow_add u (1 + n * 2) (quadraticExp n)).symm
      _ = u ^ (quadraticExp n + 2 * n + 1) := by congr 1 <;> ring
      _ = 1 := hE1
  have hs2 : u ^ 3 * u ^ (n * 4) * u ^ quadraticExp n = 1 := by
    calc
      u ^ 3 * u ^ (n * 4) * u ^ quadraticExp n =
          u ^ (3 + n * 4) * u ^ quadraticExp n := by rw [pow_add]
      _ = u ^ (3 + n * 4 + quadraticExp n) :=
        (pow_add u (3 + n * 4) (quadraticExp n)).symm
      _ = u ^ (quadraticExp n + 4 * n + 3) := by congr 1 <;> ring
      _ = 1 := hE2
  have hc1 : C u * C u ^ (n * 2) * C u ^ quadraticExp n = (1 : K[X]) := by
    calc
      C u * C u ^ (n * 2) * C u ^ quadraticExp n =
          C (u * u ^ (n * 2) * u ^ quadraticExp n) := by simp [map_mul, map_pow]
      _ = 1 := by rw [hs1]; simp
  have hc2 : C u ^ 3 * C u ^ (n * 4) * C u ^ quadraticExp n = (1 : K[X]) := by
    calc
      C u ^ 3 * C u ^ (n * 4) * C u ^ quadraticExp n =
          C (u ^ 3 * u ^ (n * 4) * u ^ quadraticExp n) := by simp [map_mul, map_pow]
      _ = 1 := by rw [hs2]; simp
  have hmul1 :
      X ^ 2 * X ^ (n * 2) * C u * C u ^ quadraticExp n * C u ^ (n * 2) =
        X ^ 2 * X ^ (n * 2) := by
    calc
      X ^ 2 * X ^ (n * 2) * C u * C u ^ quadraticExp n * C u ^ (n * 2) =
          (X ^ 2 * X ^ (n * 2)) *
            (C u * C u ^ (n * 2) * C u ^ quadraticExp n) := by ring
      _ = X ^ 2 * X ^ (n * 2) := by rw [hc1, mul_one]
  have hmul2 :
      X ^ 2 * X ^ (n * 2) * C u ^ 3 * C u ^ quadraticExp n * C u ^ (n * 4) =
        X ^ 2 * X ^ (n * 2) := by
    calc
      X ^ 2 * X ^ (n * 2) * C u ^ 3 * C u ^ quadraticExp n * C u ^ (n * 4) =
          (X ^ 2 * X ^ (n * 2)) *
            (C u ^ 3 * C u ^ (n * 4) * C u ^ quadraticExp n) := by ring
      _ = X ^ 2 * X ^ (n * 2) := by rw [hc2, mul_one]
  have hx : (X : K[X]) ^ (n.succ * 2) = X ^ 2 * X ^ (n * 2) := by
    rw [show n.succ * 2 = 2 + n * 2 by omega, pow_add]
  rw [hmul1, hmul2]
  rw [hx]
  ring

theorem rogersFineR_qdiff (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    (1 + X) * rogersFineR p u + C u * X * scalePoly u (rogersFineR p u) =
      1 + X ^ p - 2 * X ^ (2 * p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hinter :
      (1 + X) * (∑ k ∈ Finset.range n, rogersFineTerm (n + 1) u k) +
          C u * X * scalePoly u
            (∑ k ∈ Finset.range n, rogersFineTerm (n + 1) u k) =
        ∑ k ∈ Finset.range n,
          (gTerm (n + 1) u k - gTerm (n + 1) u (k + 1)) := by
    simp only [map_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact rogersFineTerm_qdiff (hu := hu) (by simpa using hk)
  have hlast :
      (1 + X) * rogersFineTerm (n + 1) u n +
          C u * X * scalePoly u (rogersFineTerm (n + 1) u n) =
        gTerm (n + 1) u n - 2 * X ^ (2 * (n + 1)) := by
    simpa using rogersFineTerm_qdiff_last hodd (Nat.succ_pos n) hu
  unfold rogersFineR
  rw [Finset.sum_range_succ]
  simp only [map_add]
  have hzero : gTerm (n + 1) u 0 = 1 + X ^ (n + 1) := by
    unfold gTerm
    simp only [qPoch_zero, quadraticExp_zero, pow_zero, mul_one, C_1,
      Nat.mul_zero, one_mul]
    exact one_add_X_mul_tail_zero hodd (Nat.succ_pos n) hu
  rw [show
    (1 + X) * ((∑ k ∈ Finset.range n, rogersFineTerm (n + 1) u k) +
          rogersFineTerm (n + 1) u n) +
        C u * X *
          (scalePoly u (∑ k ∈ Finset.range n, rogersFineTerm (n + 1) u k) +
            scalePoly u (rogersFineTerm (n + 1) u n)) =
      ((1 + X) * (∑ k ∈ Finset.range n, rogersFineTerm (n + 1) u k) +
        C u * X * scalePoly u
          (∑ k ∈ Finset.range n, rogersFineTerm (n + 1) u k)) +
      ((1 + X) * rogersFineTerm (n + 1) u n +
        C u * X * scalePoly u (rogersFineTerm (n + 1) u n)) by ring]
  rw [hinter, hlast, Finset.sum_range_sub', hzero]
  simp only [Nat.succ_eq_add_one]
  ring

private theorem scalePoly_one_sub_X_pow (hu : IsPrimitiveRoot u p) :
    scalePoly u (1 - X ^ p : K[X]) = 1 - X ^ p := by
  simp only [map_sub, map_one, map_pow, scalePoly_X, mul_pow]
  have hC : (C u : K[X]) ^ p = C (u ^ p) := (map_pow C u p).symm
  rw [hC, hu.pow_eq_one]
  simp

private theorem qdiff_unique (u : K) (H : K[X])
    (h : (1 + X) * H + C u * X * scalePoly u H = 0) : H = 0 := by
  have h' : H + X * H + C u * (X * scalePoly u H) = 0 := by
    calc
      H + X * H + C u * (X * scalePoly u H) =
          (1 + X) * H + C u * X * scalePoly u H := by ring
      _ = 0 := h
  ext n
  induction n with
  | zero =>
      have hc := congrArg (fun f : K[X] => f.coeff 0) h'
      simpa using hc
  | succ n ih =>
      have hc := congrArg (fun f : K[X] => f.coeff (n + 1)) h'
      simp only [coeff_add, coeff_X_mul, coeff_C_mul, coeff_zero] at hc
      rw [coeff_scalePoly, ih] at hc
      simpa using hc

/-- The denominator-cleared finite Rogers--Fine identity `(FRF)`. -/
theorem finiteRogersFine (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    (1 - X ^ p) * rogersFineL p u = rogersFineR p u := by
  let P : K[X] := (1 - X ^ p) * rogersFineL p u
  let H : K[X] := P - rogersFineR p u
  have hscale : scalePoly u (1 - X ^ p : K[X]) = 1 - X ^ p :=
    scalePoly_one_sub_X_pow hu
  have hP :
      (1 + X) * P + C u * X * scalePoly u P =
        1 + X ^ p - 2 * X ^ (2 * p) := by
    dsimp only [P]
    rw [map_mul, hscale]
    have hL := rogersFineL_qdiff (p := p) (u := u) hodd hp hu
    calc
      (1 + X) * ((1 - X ^ p) * rogersFineL p u) +
          C u * X * ((1 - X ^ p) * scalePoly u (rogersFineL p u)) =
        (1 - X ^ p) *
          ((1 + X) * rogersFineL p u +
            C u * X * scalePoly u (rogersFineL p u)) := by ring
      _ = (1 - X ^ p) * (1 + 2 * X ^ p) := by rw [hL]
      _ = 1 + X ^ p - 2 * X ^ (2 * p) := by
        rw [show (X : K[X]) ^ (2 * p) = X ^ p * X ^ p by
          rw [show 2 * p = p + p by omega, pow_add]]
        ring
  have hH : (1 + X) * H + C u * X * scalePoly u H = 0 := by
    dsimp only [H]
    rw [map_sub]
    have hR := rogersFineR_qdiff (p := p) (u := u) hodd hp hu
    linear_combination hP - hR
  have hz : H = 0 := qdiff_unique u H hH
  dsimp only [H, P] at hz
  exact sub_eq_zero.mp hz

end MockTheta
