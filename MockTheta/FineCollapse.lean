import MockTheta.RogersFineFinite

noncomputable section
open scoped BigOperators
namespace MockTheta
open Finset Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {p : ℕ} {u : K}

def fineL (p : ℕ) (u : K) : K[X] :=
  ∑ n ∈ range p, C ((-1 : K) ^ n * (qPoch u n)⁻¹) * X ^ n

def fineTerm (p : ℕ) (u : K) (n : ℕ) : K[X] :=
  C (u ^ (n * n) * (qPoch u n)⁻¹) * X ^ n * tailPoly p n u

def fineR (p : ℕ) (u : K) : K[X] :=
  ∑ n ∈ range p, fineTerm p u n

private def fineLTerm (u : K) (n : ℕ) : K[X] :=
  C ((-1 : K) ^ n * (qPoch u n)⁻¹) * X ^ n

private theorem fineLTerm_shift (hodd : Odd p) (hu : IsPrimitiveRoot u p)
    {n : ℕ} (hn : n + 1 < p) :
    fineLTerm u (n + 1) + scalePoly u (fineLTerm u (n + 1)) =
      -(X * fineLTerm u n) := by
  have hq : qPoch u n ≠ 0 := qPoch_ne_zero hodd hu (by omega)
  have hfac : 1 + u ^ (n + 1) ≠ 0 := one_add_pow_ne_zero hodd hu (n + 1)
  have hc :
      ((-1 : K) ^ (n + 1) * (qPoch u (n + 1))⁻¹) *
          (1 + u ^ (n + 1)) =
        -((-1 : K) ^ n * (qPoch u n)⁻¹) := by
    rw [qPoch_succ, pow_succ]
    field_simp [hq, hfac]
  unfold fineLTerm
  rw [scalePoly_C_mul_X_pow]
  rw [show
      C ((-1 : K) ^ (n + 1) * (qPoch u (n + 1))⁻¹) * X ^ (n + 1) +
          C (((-1 : K) ^ (n + 1) * (qPoch u (n + 1))⁻¹) * u ^ (n + 1)) *
            X ^ (n + 1) =
        C ((((-1 : K) ^ (n + 1) * (qPoch u (n + 1))⁻¹) *
          (1 + u ^ (n + 1)))) * X ^ (n + 1) by
      simp only [map_mul, map_add, map_one]
      ring]
  rw [hc, map_neg]
  rw [show X ^ (n + 1) = X * X ^ n by rw [pow_succ, mul_comm]]
  ring

private def fineCert (p : ℕ) (u : K) (n : ℕ) : K[X] :=
  -((1 + X) * C (1 + u ^ n) * fineTerm p u n)

theorem fineL_qdiff (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    (1 + X) * fineL p u + scalePoly u (fineL p u) = 2 + X ^ p := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  let f : ℕ → K[X] := fineLTerm u
  have hshift (k : ℕ) (hk : k ∈ range n) :
      f (k + 1) + scalePoly u (f (k + 1)) = -(X * f k) := by
    exact fineLTerm_shift hodd hu (by simpa using hk)
  have hexpand :
      (1 + X) * fineL (n + 1) u + scalePoly u (fineL (n + 1) u) =
        X * (∑ k ∈ range (n + 1), f k) +
          (∑ k ∈ range (n + 1), (f k + scalePoly u (f k))) := by
    change (1 + X) * (∑ k ∈ range (n + 1), f k) +
        scalePoly u (∑ k ∈ range (n + 1), f k) = _
    rw [map_sum, Finset.sum_add_distrib]
    ring
  rw [hexpand, Finset.sum_range_succ, Finset.sum_range_succ',
    Finset.sum_congr rfl hshift, Finset.sum_neg_distrib]
  rw [mul_add, Finset.mul_sum]
  simp only [f, fineLTerm, qPoch_zero, inv_one, mul_one, pow_zero,
    map_one]
  have hq : qPoch u n = 1 := by
    simpa [qPoch] using cyclotomicDefect hodd (Nat.succ_pos n) hu
  rw [hq]
  have hsign : (-1 : K) ^ n = 1 := by
    rcases hodd with ⟨k, hk⟩
    have hn : n = 2 * k := by omega
    rw [hn, pow_mul]
    simp
  rw [hsign]
  simp only [inv_one, mul_one, C_1]
  simp only [one_mul, Nat.succ_eq_add_one]
  rw [show X * X ^ n = X ^ (n + 1) by rw [pow_succ, mul_comm]]
  ring

private theorem fineTerm_qdiff {n : ℕ} (hn : n + 1 < p)
    (hodd : Odd p) (hu : IsPrimitiveRoot u p) :
    (1 + X) * fineTerm p u n + scalePoly u (fineTerm p u n) =
      fineCert p u (n + 1) - fineCert p u n := by
  have hq : qPoch u n ≠ 0 := qPoch_ne_zero hodd hu (by omega)
  have hfac : 1 + u ^ (n + 1) ≠ 0 := one_add_pow_ne_zero hodd hu (n + 1)
  have hb :
      (1 + u ^ (n + 1)) *
          (u ^ ((n + 1) * (n + 1)) * (qPoch u (n + 1))⁻¹) =
        u ^ (n * n + 2 * n + 1) * (qPoch u n)⁻¹ := by
    rw [qPoch_succ]
    have hexp : (n + 1) * (n + 1) = n * n + 2 * n + 1 := by ring
    rw [hexp]
    field_simp [hq, hfac]
  have hscale :
      scalePoly u (fineTerm p u n) =
        C ((u ^ (n * n) * (qPoch u n)⁻¹) * u ^ n) * X ^ n *
          ((1 + X) * tailPoly p (n + 1) u) := by
    unfold fineTerm
    rw [map_mul, scalePoly_C_mul_X_pow, scalePoly_tailPoly hn hu]
  unfold fineCert
  rw [hscale]
  unfold fineTerm
  rw [tailPoly_succ hn]
  have hbC :
      C (1 + u ^ (n + 1)) *
          C (u ^ ((n + 1) * (n + 1)) * (qPoch u (n + 1))⁻¹) =
        C (u ^ (n * n + 2 * n + 1) * (qPoch u n)⁻¹) := by
    rw [← map_mul, hb]
  rw [show
      (1 + X) * C (1 + u ^ (n + 1)) *
          (C (u ^ ((n + 1) * (n + 1)) * (qPoch u (n + 1))⁻¹) *
            X ^ (n + 1) * tailPoly p (n + 1) u) =
        (1 + X) *
          (C (1 + u ^ (n + 1)) *
            C (u ^ ((n + 1) * (n + 1)) * (qPoch u (n + 1))⁻¹)) *
          X ^ (n + 1) * tailPoly p (n + 1) u by ring]
  rw [hbC]
  simp only [map_add, map_one, map_mul, pow_add, pow_succ]
  have hpow2 : C (u ^ n) ^ 2 = C (u ^ (n * 2)) := by
    rw [← map_pow, ← pow_mul]
  have hpow2' : C (u ^ (2 * n)) = C (u ^ n) ^ 2 := by
    rw [mul_comm, ← hpow2]
  rw [hpow2']
  ring

private theorem fineTerm_qdiff_last (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    (1 + X) * fineTerm p u (p - 1) +
        scalePoly u (fineTerm p u (p - 1)) =
      -X ^ p - fineCert p u (p - 1) := by
  unfold fineCert
  unfold fineTerm
  rw [tailPoly_at_last hp]
  have hq : qPoch u (p - 1) = 1 := by
    simpa [qPoch] using cyclotomicDefect hodd hp hu
  rw [hq]
  simp only [inv_one, mul_one, map_mul, map_add, map_one, scalePoly_C,
    scalePoly_X, map_pow]
  have hpow : u ^ ((p - 1) * (p - 1)) = u := by
    conv_rhs => rw [← pow_one u]
    apply (hu.isOfFinOrder hp.ne').pow_eq_pow_iff_modEq.2
    rw [← hu.eq_orderOf]
    apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
    push_cast
    have hpcast : ((p - 1 : ℕ) : ZMod p) = -1 := by
      have hc := congrArg (fun x : ℕ => (x : ZMod p))
        (show p - 1 + 1 = p by omega)
      push_cast at hc
      rw [ZMod.natCast_self] at hc
      linear_combination hc
    rw [hpcast]
    ring
  have hpowC : (C u : K[X]) ^ ((p - 1) * (p - 1)) = C u := by
    rw [← map_pow, hpow]
  rw [hpowC]
  have hpred : u ^ (p - 1) * u = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    exact hu.pow_eq_one
  have hpredC : (C u : K[X]) ^ (p - 1) * C u = 1 := by
    rw [← map_pow, ← map_mul, hpred, map_one]
  simp only [mul_pow]
  ring_nf
  have hprod : C u * (C u : K[X]) ^ (p - 1) = 1 := by
    rw [mul_comm, hpredC]
  have hx : X * X ^ (p - 1) = (X : K[X]) ^ p := by
    calc
      _ = X ^ (p - 1) * X := mul_comm _ _
      _ = X ^ (p - 1 + 1) := (pow_succ X (p - 1)).symm
      _ = _ := by congr 1 <;> omega
  have hA : X ^ (p - 1) * C u * (C u : K[X]) ^ (p - 1) = X ^ (p - 1) := by
    calc
      _ = X ^ (p - 1) * (C u * (C u : K[X]) ^ (p - 1)) := by ring
      _ = _ := by rw [hprod, mul_one]
  have hB : X * X ^ (p - 1) * C u * (C u : K[X]) ^ (p - 1) = X ^ p := by
    calc
      _ = (X * X ^ (p - 1)) * (C u * (C u : K[X]) ^ (p - 1)) := by ring
      _ = _ := by rw [hprod, mul_one, hx]
  rw [hA, hB]
  ring

theorem fineR_qdiff (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    (1 + X) * fineR p u + scalePoly u (fineR p u) = 2 + X ^ p := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  have hinter :
      (1 + X) * (∑ k ∈ range n, fineTerm (n + 1) u k) +
          scalePoly u (∑ k ∈ range n, fineTerm (n + 1) u k) =
        ∑ k ∈ range n,
          (fineCert (n + 1) u (k + 1) - fineCert (n + 1) u k) := by
    simp only [map_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact fineTerm_qdiff (hodd := hodd) (hu := hu) (by simpa using hk)
  have hlast :
      (1 + X) * fineTerm (n + 1) u n +
          scalePoly u (fineTerm (n + 1) u n) =
        -X ^ (n + 1) - fineCert (n + 1) u n := by
    simpa using fineTerm_qdiff_last (p := n + 1) hodd (Nat.succ_pos n) hu
  unfold fineR
  rw [Finset.sum_range_succ]
  simp only [map_add]
  rw [show
      (1 + X) * ((∑ k ∈ range n, fineTerm (n + 1) u k) +
          fineTerm (n + 1) u n) +
        (scalePoly u (∑ k ∈ range n, fineTerm (n + 1) u k) +
          scalePoly u (fineTerm (n + 1) u n)) =
      ((1 + X) * (∑ k ∈ range n, fineTerm (n + 1) u k) +
        scalePoly u (∑ k ∈ range n, fineTerm (n + 1) u k)) +
      ((1 + X) * fineTerm (n + 1) u n +
        scalePoly u (fineTerm (n + 1) u n)) by ring]
  rw [hinter, hlast, Finset.sum_range_sub]
  have hzero : fineCert (n + 1) u 0 = -2 * (1 + X ^ (n + 1)) := by
    unfold fineCert fineTerm
    norm_num [qPoch_zero]
    calc
      (1 + X) * C 2 * tailPoly (n + 1) 0 u =
          2 * ((1 + X) * tailPoly (n + 1) 0 u) := by
            rw [show C (2 : K) = (2 : K[X]) from Polynomial.C_ofNat 2]
            ring
      _ = _ := by rw [one_add_X_mul_tail_zero hodd (Nat.succ_pos n) hu]
  rw [hzero]
  simp only [Nat.succ_eq_add_one]
  ring

private theorem fine_qdiff_unique (hodd : Odd p) (hu : IsPrimitiveRoot u p)
    (H : K[X]) (h : (1 + X) * H + scalePoly u H = 0) : H = 0 := by
  have h' : H + X * H + scalePoly u H = 0 := by
    calc
      _ = (1 + X) * H + scalePoly u H := by ring
      _ = 0 := h
  ext n
  simp only [coeff_zero]
  induction n with
  | zero =>
      have hc := congrArg (fun f : K[X] => f.coeff 0) h'
      simp at hc
      exact hc
  | succ n ih =>
      have hc := congrArg (fun f : K[X] => f.coeff (n + 1)) h'
      simp only [coeff_add, coeff_X_mul, coeff_scalePoly, coeff_zero] at hc
      rw [ih] at hc
      have hfac : 1 + u ^ (n + 1) ≠ 0 := one_add_pow_ne_zero hodd hu (n + 1)
      apply (mul_left_cancel₀ hfac)
      linear_combination hc

/-- The finite Rogers--Fine identity specialized to Fine's collapse. Both sides
satisfy the same polynomial q-difference equation, whose solution is unique. -/
theorem finiteFine (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) : fineL p u = fineR p u := by
  let H := fineL p u - fineR p u
  have hH : (1 + X) * H + scalePoly u H = 0 := by
    dsimp only [H]
    rw [map_sub]
    have hL := fineL_qdiff (p := p) (u := u) hodd hp hu
    have hR := fineR_qdiff (p := p) (u := u) hodd hp hu
    linear_combination hL - hR
  exact sub_eq_zero.mp (fine_qdiff_unique hodd hu H hH)

private theorem eval_tail_eq_inv (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) {n : ℕ} (hn : n < p) :
    eval 1 (tailPoly p n u) = (qPoch u n)⁻¹ := by
  have hlen : p - 1 = n + (p - (n + 1)) := by omega
  have hdef := cyclotomicDefect hodd hp hu
  have hmul : qPoch u n * eval 1 (tailPoly p n u) = 1 := by
    unfold qPoch at hdef ⊢
    unfold tailPoly
    simp only [eval_prod, eval_add, eval_one, eval_mul, eval_C, eval_X,
      mul_one]
    rw [hlen, Finset.prod_range_add] at hdef
    convert hdef using 1 <;> ring
  have hq : qPoch u n ≠ 0 := qPoch_ne_zero hodd hu hn
  field_simp [hq]
  simpa [mul_comm] using hmul

/-- Fine's collapse in its finite root-of-unity form. -/
theorem fineCollapse (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    T p u = ∑ n ∈ range p, (-1 : K) ^ n * (qPoch u n)⁻¹ := by
  have hf := congrArg (eval (1 : K)) (finiteFine hodd hp hu)
  rw [show eval 1 (fineL p u) =
      ∑ n ∈ range p, (-1 : K) ^ n * (qPoch u n)⁻¹ by
    unfold fineL
    rw [eval_finsetSum]
    apply Finset.sum_congr rfl
    intro n hn
    simp] at hf
  rw [show eval 1 (fineR p u) = T p u by
    unfold fineR T
    rw [eval_finsetSum]
    apply Finset.sum_congr rfl
    intro n hn
    unfold fineTerm
    simp only [eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    rw [eval_tail_eq_inv hodd hp hu (by simpa using hn)]
    ring] at hf
  exact hf.symm

private theorem qPoch_inv_complement (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) {s : ℕ} (hs : s < p) :
    qPoch u⁻¹ (p - 1 - s) = (qPoch u s)⁻¹ := by
  let len := p - 1 - s
  have hlen : len = p - (s + 1) := by dsimp [len]; omega
  have hrev :
      qPoch u⁻¹ len =
        ∏ j ∈ range len, (1 + u ^ (s + 1 + j)) := by
    unfold qPoch
    rw [← Finset.prod_range_reflect (fun j => 1 + (u⁻¹) ^ (j + 1)) len]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [mem_range] at hj
    congr 1
    have hexp : len - 1 - j + 1 + (s + 1 + j) = p := by
      dsimp [len]
      omega
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, hexp, hu.pow_eq_one]
  rw [hrev, hlen]
  have hmul :
      qPoch u s * (∏ j ∈ range (p - (s + 1)),
        (1 + u ^ (s + 1 + j))) = 1 := by
    have hdef := cyclotomicDefect hodd hp hu
    unfold qPoch at hdef ⊢
    have htotal : p - 1 = s + (p - (s + 1)) := by omega
    rw [htotal, Finset.prod_range_add] at hdef
    convert hdef using 1 <;> ring
  have hq : qPoch u s ≠ 0 := qPoch_ne_zero hodd hu hs
  field_simp [hq]
  simpa [mul_comm] using hmul

/-- Reindexing the finite Fine collapse gives the reverse-Fine sum. -/
theorem reverseFine (hodd : Odd p) (hp : 0 < p)
    (hu : IsPrimitiveRoot u p) :
    T p u = reverseFineSum p u⁻¹ := by
  rw [fineCollapse hodd hp hu]
  unfold reverseFineSum
  rw [← Finset.sum_range_reflect
    (fun n => (-1 : K) ^ n * qPoch u⁻¹ n) p]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [mem_range] at hs
  rw [qPoch_inv_complement hodd hp hu hs]
  have hsign : (-1 : K) ^ (p - 1 - s) = (-1 : K) ^ s := by
    rcases hodd with ⟨k, hk⟩
    rcases Nat.even_or_odd s with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hj' : s = 2 * j := by omega
      have hsub : p - 1 - s = 2 * (k - j) := by omega
      rw [hsub, hj']
      simp only [pow_mul, neg_one_sq, one_pow]
    · have hj' : s = 2 * j + 1 := by omega
      have hsub : p - 1 - s = 2 * (k - j - 1) + 1 := by omega
      rw [hsub, hj']
      simp only [pow_add, pow_mul, neg_one_sq, one_pow, pow_one,
        one_mul]
  rw [hsign]

end MockTheta
