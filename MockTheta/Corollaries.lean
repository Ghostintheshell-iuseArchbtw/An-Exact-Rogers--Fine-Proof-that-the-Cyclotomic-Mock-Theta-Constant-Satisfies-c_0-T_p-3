import MockTheta.AllCoordinates
import MockTheta.CentralTheorem
import Mathlib.RingTheory.Trace.Basic

noncomputable section
open scoped BigOperators
namespace MockTheta
open Finset Polynomial

/-- Redundant coefficient of `ζ^m` in the weighted formula. -/
def redundantCoeff (p m : ℕ) : ℚ :=
  (p : ℚ)⁻¹ *
    ∑ n ∈ (range p).filter (fun n => exponentResidue p n = m),
      ((weight p n : ℤ) : ℚ)

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [Field L] [Algebra ℚ L]
variable [IsCyclotomicExtension {p} ℚ L]
variable {ζ : L}

theorem weighted_expansion (hp7 : 7 ≤ p) (hζ : IsPrimitiveRoot ζ p) :
    T p ζ =
      ∑ m ∈ range p, algebraMap ℚ L (redundantCoeff p m) * ζ ^ m := by
  rw [weighted_formula hp7 hζ]
  have hmaps : ∀ n ∈ range p, exponentResidue p n ∈ range p := by
    intro n hn
    exact mem_range.mpr (ZMod.val_lt _)
  have hpow (n : ℕ) :
      (ζ⁻¹) ^ quadraticExp n = ζ ^ exponentResidue p n :=
    inv_pow_eq_pow_exponentResidue hp7 hζ n
  simp_rw [hpow]
  rw [← sum_fiberwise_of_maps_to hmaps
    (fun n => (((weight p n : ℤ) : L)) * ζ ^ exponentResidue p n)]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro m hm
  unfold redundantCoeff
  rw [map_mul, map_inv₀]
  simp only [map_natCast, map_sum, map_intCast]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply sum_congr rfl
  intro n hn
  have hnm : exponentResidue p n = m := (mem_filter.mp hn).2
  rw [hnm]
  ring

/-- Every genuine coordinate is its redundant coefficient minus the final
redundant coefficient. -/
theorem cCoeff_T_eq_redundant_sub (hp7 : 7 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) {m : ℕ} (hm : m < p - 1) :
    cCoeff (K := ℚ) hζ m (T p ζ) =
      redundantCoeff p m - redundantCoeff p (p - 1) := by
  rw [weighted_expansion hp7 hζ]
  exact cCoeff_redundant_sum hζ Fact.out
    (cyclotomic.irreducible_rat (by omega)) (redundantCoeff p) hm

theorem exponentResidue_eq_iff (hp7 : 7 ≤ p) {n m : ℕ} (hm : m < p) :
    exponentResidue p n = m ↔
      (quadraticExp n : ZMod p) = -(m : ZMod p) := by
  constructor
  · intro h
    have hc := congrArg (fun x : ℕ => (x : ZMod p)) h
    unfold exponentResidue at hc
    rw [ZMod.natCast_zmod_val] at hc
    linear_combination -hc
  · intro h
    unfold exponentResidue
    have hz : -(quadraticExp n : ZMod p) = (m : ZMod p) := by
      linear_combination -h
    rw [hz, ZMod.val_natCast, Nat.mod_eq_of_lt hm]

theorem residue_pred_support (hp7 : 7 ≤ p) :
    (range p).filter (fun n => exponentResidue p n = p - 1) =
      {p - 1, specialRoot p + 1} := by
  rw [← oneSupport hp7]
  apply filter_congr
  intro n hn
  have hpcast := cast_pred_order hp7
  rw [exponentResidue_eq_iff hp7 (by omega), hpcast]
  simp

theorem redundantCoeff_pred (hp7 : 7 ≤ p) :
    redundantCoeff p (p - 1) =
      (p : ℚ)⁻¹ *
        (((weight p (p - 1) : ℤ) : ℚ) +
          ((weight p (specialRoot p + 1) : ℤ) : ℚ)) := by
  unfold redundantCoeff
  rw [residue_pred_support hp7]
  rw [sum_insert (by simpa using (specialRoot_succ_ne_pred hp7).symm),
    sum_singleton]

theorem specialRoot_of_eq_six_mul_add_one (hp7 : 7 ≤ p)
    {h : ℕ} (hpform : p = 6 * h + 1) : specialRoot p = 2 * h := by
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
    rw [specialRoot_cast hp7]
    have h3 : (3 : ZMod p) ≠ 0 := by
      intro hz
      have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
      have hle := Nat.le_of_dvd (by omega : 0 < 3) hd
      omega
    apply mul_left_cancel₀ h3
    field_simp [h3]
    push_cast
    have hpcast := congrArg (fun x : ℕ => (x : ZMod p)) hpform
    push_cast at hpcast
    rw [ZMod.natCast_self] at hpcast
    linear_combination hpcast
  · exact specialRoot_lt hp7
  · omega

theorem specialRoot_of_eq_six_mul_add_five (hp7 : 7 ≤ p)
    {h : ℕ} (hpform : p = 6 * h + 5) : specialRoot p = 4 * h + 3 := by
  apply Nat.ModEq.eq_of_lt_of_lt
  · apply (ZMod.natCast_eq_natCast_iff _ _ p).mp
    rw [specialRoot_cast hp7]
    have h3 : (3 : ZMod p) ≠ 0 := by
      intro hz
      have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
      have hle := Nat.le_of_dvd (by omega : 0 < 3) hd
      omega
    apply mul_left_cancel₀ h3
    field_simp [h3]
    push_cast
    have hpcast := congrArg (fun x : ℕ => (x : ZMod p)) hpform
    push_cast at hpcast
    rw [ZMod.natCast_self] at hpcast
    linear_combination 2 * hpcast
  · exact specialRoot_lt hp7
  · omega

theorem redundantCoeff_pred_of_eq_six_mul_add_one (hp7 : 7 ≤ p)
    {h : ℕ} (hpform : p = 6 * h + 1) :
    redundantCoeff p (p - 1) = -1 := by
  rw [redundantCoeff_pred hp7,
    specialRoot_of_eq_six_mul_add_one hp7 hpform]
  have hhalf : (3 * (6 * (h : ℤ) + 1) - 1) / 2 = 9 * h + 1 := by
    omega
  have hpred : 6 * h + 1 - 1 = 6 * h := by omega
  unfold weight
  rw [hpform]
  rw [hpred]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hhalf]
  push_cast
  field_simp
  ring

theorem redundantCoeff_pred_of_eq_six_mul_add_five (hp7 : 7 ≤ p)
    {h : ℕ} (hpform : p = 6 * h + 5) :
    redundantCoeff p (p - 1) = -2 := by
  rw [redundantCoeff_pred hp7,
    specialRoot_of_eq_six_mul_add_five hp7 hpform]
  have hhalf : (3 * (6 * (h : ℤ) + 5) - 1) / 2 = 9 * h + 7 := by
    omega
  have hpred : 6 * h + 5 - 1 = 6 * h + 4 := by omega
  unfold weight
  rw [hpform]
  rw [hpred]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hhalf]
  push_cast
  field_simp
  ring

theorem sum_weight_rat (hp7 : 7 ≤ p) :
    ∑ n ∈ range p, ((weight p n : ℤ) : ℚ) = p := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  simp_rw [cast_weight (K := ℚ) hodd]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]
  rw [← Finset.mul_sum]
  have hsumNat := Finset.sum_range_id_mul_two p
  have hsumRat :
      (2 : ℚ) * (∑ n ∈ range p, (n : ℚ)) = p * (p - 1) := by
    have hc := congrArg (fun n : ℕ => (n : ℚ)) hsumNat
    push_cast at hc
    rw [Nat.cast_sub hp.one_le] at hc
    linear_combination hc
  push_cast
  have hsumEq : (∑ n ∈ range p, (n : ℚ)) = p * (p - 1) / 2 := by
    linarith [hsumRat]
  rw [hsumEq]
  ring

theorem sum_redundantCoeff (hp7 : 7 ≤ p) :
    ∑ m ∈ range p, redundantCoeff p m = 1 := by
  unfold redundantCoeff
  rw [← Finset.mul_sum]
  have hmaps : ∀ n ∈ range p, exponentResidue p n ∈ range p := by
    intro n hn
    exact mem_range.mpr (ZMod.val_lt _)
  rw [sum_fiberwise_of_maps_to hmaps
    (fun n => ((weight p n : ℤ) : ℚ))]
  rw [sum_weight_rat hp7]
  have hpQ : (p : ℚ) ≠ 0 := by norm_num; omega
  field_simp

/-- Sum of all genuine power-basis coordinates (the manuscript's `T_p(1)`). -/
def TAtOne (hζ : IsPrimitiveRoot ζ p) : ℚ :=
  ∑ m ∈ range (p - 1), cCoeff (K := ℚ) hζ m (T p ζ)

theorem TAtOne_eq_one_sub (hp7 : 7 ≤ p) (hζ : IsPrimitiveRoot ζ p) :
    TAtOne hζ = 1 - p * redundantCoeff p (p - 1) := by
  unfold TAtOne
  rw [show (∑ m ∈ range (p - 1), cCoeff (K := ℚ) hζ m (T p ζ)) =
      ∑ m ∈ range (p - 1),
        (redundantCoeff p m - redundantCoeff p (p - 1)) by
    apply sum_congr rfl
    intro m hm
    exact cCoeff_T_eq_redundant_sub hp7 hζ (mem_range.mp hm)]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hsplit :
      (∑ m ∈ range (p - 1), redundantCoeff p m) +
          redundantCoeff p (p - 1) = 1 := by
    calc
      _ = ∑ m ∈ range ((p - 1) + 1), redundantCoeff p m :=
        (sum_range_succ (fun m => redundantCoeff p m) (p - 1)).symm
      _ = ∑ m ∈ range p, redundantCoeff p m := by congr 2 <;> omega
      _ = 1 := sum_redundantCoeff hp7
  rw [Finset.card_range]
  have hp1 : 1 ≤ p := by omega
  rw [Nat.cast_sub hp1]
  push_cast
  linear_combination hsplit

theorem TAtOne_of_eq_six_mul_add_one (hp7 : 7 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) {h : ℕ} (hpform : p = 6 * h + 1) :
    TAtOne hζ = p + 1 := by
  rw [TAtOne_eq_one_sub hp7 hζ,
    redundantCoeff_pred_of_eq_six_mul_add_one hp7 hpform]
  ring

theorem TAtOne_of_eq_six_mul_add_five (hp7 : 7 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) {h : ℕ} (hpform : p = 6 * h + 5) :
    TAtOne hζ = 2 * p + 1 := by
  rw [TAtOne_eq_one_sub hp7 hζ,
    redundantCoeff_pred_of_eq_six_mul_add_five hp7 hpform]
  ring

theorem trace_pow_of_pos_lt (hζ : IsPrimitiveRoot ζ p)
    {n : ℕ} (hn0 : n ≠ 0) (hn : n < p) :
    Algebra.trace ℚ L (ζ ^ n) = -1 := by
  have hp : p.Prime := Fact.out
  have hndiv : ¬p ∣ n := by
    intro hd
    exact hn0 (Nat.eq_zero_of_dvd_of_lt hd hn)
  have hcop : n.Coprime p := ((hp.coprime_iff_not_dvd).2 hndiv).symm
  have hroot := hζ.pow_of_coprime n hcop
  let pb := hroot.powerBasis ℚ
  calc
    Algebra.trace ℚ L (ζ ^ n) = Algebra.trace ℚ L pb.gen := by
      change Algebra.trace ℚ L (ζ ^ n) =
        Algebra.trace ℚ L (hroot.powerBasis ℚ).gen
      rw [hroot.powerBasis_gen ℚ]
    _ = -(minpoly ℚ pb.gen).nextCoeff :=
      PowerBasis.trace_gen_eq_nextCoeff_minpoly pb
    _ = -1 := by
      rw [show minpoly ℚ pb.gen = cyclotomic p ℚ by
        change minpoly ℚ (hroot.powerBasis ℚ).gen = cyclotomic p ℚ
        rw [hroot.powerBasis_gen ℚ]
        exact (hroot.minpoly_eq_cyclotomic_of_irreducible
          (cyclotomic.irreducible_rat hp.pos)).symm]
      rw [cyclotomic_prime ℚ p]
      have hdegree :
          (∑ i ∈ range p, (X : ℚ[X]) ^ i).natDegree = p - 1 := by
        rw [← cyclotomic_prime ℚ p, natDegree_cyclotomic,
          Nat.totient_prime hp]
      rw [nextCoeff_of_natDegree_pos (by rw [hdegree]; omega), hdegree]
      simp
      omega

theorem trace_one_prime (hζ : IsPrimitiveRoot ζ p) :
    Algebra.trace ℚ L 1 = p - 1 := by
  have hp : p.Prime := Fact.out
  rw [← map_one (algebraMap ℚ L), Algebra.trace_algebraMap]
  rw [(hζ.powerBasis ℚ).finrank, hζ.powerBasis_dim ℚ,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible
      (cyclotomic.irreducible_rat hp.pos),
    natDegree_cyclotomic, Nat.totient_prime hp]
  simp only [nsmul_eq_mul, mul_one]
  rw [Nat.cast_sub hp.one_le]
  norm_num

theorem trace_T_eq (hp7 : 7 ≤ p) (hζ : IsPrimitiveRoot ζ p) :
    Algebra.trace ℚ L (T p ζ) =
      p * redundantCoeff p 0 - 1 := by
  rw [weighted_expansion hp7 hζ, map_sum]
  have hrange : range p = range ((p - 1) + 1) := by congr 1 <;> omega
  rw [hrange, sum_range_succ']
  simp only [pow_zero]
  rw [← Algebra.smul_def, map_smul, trace_one_prime hζ, smul_eq_mul]
  rw [show (∑ x ∈ range (p - 1),
      Algebra.trace ℚ L
        (algebraMap ℚ L (redundantCoeff p (x + 1)) * ζ ^ (x + 1))) =
      ∑ x ∈ range (p - 1), -redundantCoeff p (x + 1) by
    apply sum_congr rfl
    intro x hx
    rw [← Algebra.smul_def, map_smul,
      trace_pow_of_pos_lt hζ (by omega) (by
        simp only [mem_range] at hx
        omega),
      smul_eq_mul]
    ring]
  rw [Finset.sum_neg_distrib]
  have htotal := sum_redundantCoeff hp7
  rw [hrange, sum_range_succ'] at htotal
  push_cast
  have hsum :
      (∑ x ∈ range (p - 1), redundantCoeff p (x + 1)) =
        1 - redundantCoeff p 0 := by
    linarith [htotal]
  rw [hsum]
  ring

theorem trace_T_eq_three_p_sub_TAtOne (hp7 : 7 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) :
    Algebra.trace ℚ L (T p ζ) = 3 * p - TAtOne hζ := by
  have hc := cCoeff_T_eq_redundant_sub hp7 hζ (m := 0) (by omega)
  rw [cCoeff_zero_eq_c0 hζ Fact.out
      (cyclotomic.irreducible_rat (by omega)),
    c0_T_eq_three hp7 hζ] at hc
  rw [trace_T_eq hp7 hζ, TAtOne_eq_one_sub hp7 hζ]
  push_cast
  have hc' : redundantCoeff p 0 = 3 + redundantCoeff p (p - 1) := by
    linarith [hc]
  rw [hc']
  ring

theorem trace_T_of_eq_six_mul_add_one (hp7 : 7 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) {h : ℕ} (hpform : p = 6 * h + 1) :
    Algebra.trace ℚ L (T p ζ) = 2 * p - 1 := by
  rw [trace_T_eq_three_p_sub_TAtOne hp7 hζ,
    TAtOne_of_eq_six_mul_add_one hp7 hζ hpform]
  ring

theorem trace_T_of_eq_six_mul_add_five (hp7 : 7 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) {h : ℕ} (hpform : p = 6 * h + 5) :
    Algebra.trace ℚ L (T p ζ) = p - 1 := by
  rw [trace_T_eq_three_p_sub_TAtOne hp7 hζ,
    TAtOne_of_eq_six_mul_add_five hp7 hζ hpform]
  ring

/-- The natural representatives producing redundant exponent `m`. -/
def residueFiber (p m : ℕ) : Finset ℕ :=
  (range p).filter (fun n => exponentResidue p n = m)

theorem mem_residueFiber {m n : ℕ} :
    n ∈ residueFiber p m ↔ n < p ∧ exponentResidue p n = m := by
  simp [residueFiber]

private theorem three_ne_zero_zmod (hp7 : 7 ≤ p) : (3 : ZMod p) ≠ 0 := by
  intro hz
  have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
  have hle := Nat.le_of_dvd (by omega : 0 < 3) hd
  omega

private theorem two_ne_zero_zmod (hp7 : 7 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro hz
  have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
  have hle := Nat.le_of_dvd (by omega : 0 < 2) hd
  omega

theorem residue_equation_iff (hp7 : 7 ≤ p) {m n : ℕ}
    (hm : m < p) :
    exponentResidue p n = m ↔
      3 * (n : ZMod p) ^ 2 + (n : ZMod p) + 2 * (m : ZMod p) = 0 := by
  rw [exponentResidue_eq_iff hp7 hm]
  have hd := zmod_quadraticExp_double (p := p) n
  have h2 := two_ne_zero_zmod hp7
  constructor
  · intro h
    rw [h] at hd
    linear_combination -hd
  · intro h
    apply mul_left_cancel₀ h2
    rw [hd]
    linear_combination h

private theorem nat_eq_of_zmod_eq {r s : ℕ} (hr : r < p) (hs : s < p)
    (h : (r : ZMod p) = (s : ZMod p)) : r = s := by
  apply Nat.ModEq.eq_of_lt_of_lt
  · exact (ZMod.natCast_eq_natCast_iff r s p).mp h
  · exact hr
  · exact hs

theorem distinct_fiber_roots_cast_sum (hp7 : 7 ≤ p) {m r s : ℕ}
    (hr : r ∈ residueFiber p m) (hs : s ∈ residueFiber p m)
    (hrs : r ≠ s) :
    ((r + s : ℕ) : ZMod p) = (specialRoot p : ZMod p) := by
  have hr' := (mem_residueFiber.mp hr)
  have hs' := (mem_residueFiber.mp hs)
  have hm : m < p := by
    rw [← hr'.2]
    exact ZMod.val_lt _
  have hQr := (residue_equation_iff hp7 hm).mp hr'.2
  have hQs := (residue_equation_iff hp7 hm).mp hs'.2
  have hfac :
      ((r : ZMod p) - (s : ZMod p)) *
        (3 * ((r : ZMod p) + (s : ZMod p)) + 1) = 0 := by
    linear_combination hQr - hQs
  have hdiff : (r : ZMod p) - (s : ZMod p) ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    exact hrs (nat_eq_of_zmod_eq hr'.1 hs'.1 heq)
  have hlin := (mul_eq_zero.mp hfac).resolve_left hdiff
  have ha := specialRoot_equation hp7
  have h3 := three_ne_zero_zmod hp7
  apply mul_left_cancel₀ h3
  push_cast
  linear_combination hlin - ha

theorem distinct_fiber_roots_sum (hp7 : 7 ≤ p) {m r s : ℕ}
    (hr : r ∈ residueFiber p m) (hs : s ∈ residueFiber p m)
    (hrs : r ≠ s) :
    r + s = specialRoot p ∨ r + s = specialRoot p + p := by
  have hrlt := (mem_residueFiber.mp hr).1
  have hslt := (mem_residueFiber.mp hs).1
  have halt := specialRoot_lt hp7
  have hc := distinct_fiber_roots_cast_sum hp7 hr hs hrs
  have hmod : r + s ≡ specialRoot p [MOD p] :=
    (ZMod.natCast_eq_natCast_iff _ _ p).mp hc
  have hrem : (r + s) % p = specialRoot p := by
    change (r + s) % p = specialRoot p % p at hmod
    rw [Nat.mod_eq_of_lt halt] at hmod
    exact hmod
  by_cases hlt : r + s < p
  · left
    rw [Nat.mod_eq_of_lt hlt] at hrem
    exact hrem
  · right
    have hge : p ≤ r + s := by omega
    have hsub_lt : r + s - p < p := by omega
    have hrem' : (r + s) % p = r + s - p := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub_lt]
    omega

theorem residueFiber_card_le_two (hp7 : 7 ≤ p) (m : ℕ) :
    #(residueFiber p m) ≤ 2 := by
  by_cases he : residueFiber p m = ∅
  · simp [he]
  obtain ⟨r, hr⟩ := nonempty_iff_ne_empty.mpr he
  by_cases hone : residueFiber p m ⊆ {r}
  · exact (card_le_card hone).trans (by simp)
  obtain ⟨s, hs, hsr⟩ := Finset.not_subset.mp hone
  have hrs : r ≠ s := Ne.symm (by simpa using hsr)
  have hsub : residueFiber p m ⊆ {r, s} := by
    intro t ht
    simp only [mem_insert, mem_singleton]
    by_cases htr : t = r
    · exact Or.inl htr
    right
    have hrsCast := distinct_fiber_roots_cast_sum hp7 hr hs hrs
    have hrtCast := distinct_fiber_roots_cast_sum hp7 hr ht (Ne.symm htr)
    have hslt := (mem_residueFiber.mp hs).1
    have htlt := (mem_residueFiber.mp ht).1
    symm
    apply nat_eq_of_zmod_eq hslt htlt
    push_cast at hrsCast hrtCast
    linear_combination hrsCast - hrtCast
  exact (card_le_card hsub).trans card_le_two

private def otherRoot (p r : ℕ) [Fact p.Prime] : ℕ :=
  ((specialRoot p : ZMod p) - (r : ZMod p)).val

private theorem otherRoot_lt (r : ℕ) : otherRoot p r < p :=
  ZMod.val_lt _

private theorem otherRoot_cast (r : ℕ) :
    (otherRoot p r : ZMod p) =
      (specialRoot p : ZMod p) - (r : ZMod p) := by
  exact ZMod.natCast_zmod_val _

private theorem otherRoot_mem (hp7 : 7 ≤ p) {m r : ℕ}
    (hr : r ∈ residueFiber p m) : otherRoot p r ∈ residueFiber p m := by
  have hr' := mem_residueFiber.mp hr
  have hm : m < p := by
    rw [← hr'.2]
    exact ZMod.val_lt _
  apply mem_residueFiber.mpr
  refine ⟨otherRoot_lt r, (residue_equation_iff hp7 hm).mpr ?_⟩
  rw [otherRoot_cast]
  have hQr := (residue_equation_iff hp7 hm).mp hr'.2
  have ha := specialRoot_equation hp7
  linear_combination
    ((specialRoot p : ZMod p) - 2 * (r : ZMod p)) * ha + hQr

theorem singleton_fiber_root_sum (hp7 : 7 ≤ p) {m r : ℕ}
    (hf : residueFiber p m = {r}) :
    2 * r = specialRoot p ∨ 2 * r = specialRoot p + p := by
  have hr : r ∈ residueFiber p m := by simp [hf]
  have ho := otherRoot_mem hp7 hr
  rw [hf, mem_singleton] at ho
  have hc : ((2 * r : ℕ) : ZMod p) = (specialRoot p : ZMod p) := by
    have hor := otherRoot_cast (p := p) r
    rw [ho] at hor
    push_cast at hor ⊢
    linear_combination hor
  have hrlt := (mem_residueFiber.mp hr).1
  have halt := specialRoot_lt hp7
  have hmod : 2 * r ≡ specialRoot p [MOD p] :=
    (ZMod.natCast_eq_natCast_iff _ _ p).mp hc
  have hrem : (2 * r) % p = specialRoot p := by
    change (2 * r) % p = specialRoot p % p at hmod
    rw [Nat.mod_eq_of_lt halt] at hmod
    exact hmod
  by_cases hlt : 2 * r < p
  · left
    rw [Nat.mod_eq_of_lt hlt] at hrem
    exact hrem
  · right
    have hge : p ≤ 2 * r := by omega
    have hsub_lt : 2 * r - p < p := by omega
    have hrem' : (2 * r) % p = 2 * r - p := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub_lt]
    omega

theorem redundantCoeff_eq_fiber (m : ℕ) :
    redundantCoeff p m =
      (p : ℚ)⁻¹ *
        ∑ n ∈ residueFiber p m, ((weight p n : ℤ) : ℚ) := by
  rfl

theorem cCoeff_T_mem_four_of_eq_six_mul_add_one (hp7 : 7 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) {h m : ℕ} (hpform : p = 6 * h + 1)
    (hm : m < p - 1) :
    cCoeff (K := ℚ) hζ m (T p ζ) ∈ ({0, 1, 2, 3} : Finset ℚ) := by
  rw [cCoeff_T_eq_redundant_sub hp7 hζ hm,
    redundantCoeff_pred_of_eq_six_mul_add_one hp7 hpform]
  have hcard := residueFiber_card_le_two hp7 m
  have hcases : #(residueFiber p m) = 0 ∨
      #(residueFiber p m) = 1 ∨ #(residueFiber p m) = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have hf : residueFiber p m = ∅ := card_eq_zero.mp hzero
    rw [redundantCoeff_eq_fiber, hf]
    norm_num
  · obtain ⟨r, hf⟩ := card_eq_one.mp hone
    have hrsum := singleton_fiber_root_sum hp7 hf
    rw [redundantCoeff_eq_fiber, hf, sum_singleton]
    rw [hpform]
    have hhalf :
        (3 * (6 * (h : ℤ) + 1) - 1) / 2 = 9 * h + 1 := by omega
    rcases hrsum with hrsum | hrsum
    · have hr : r = h := by
        rw [specialRoot_of_eq_six_mul_add_one hp7 hpform] at hrsum
        omega
      rw [hr]
      unfold weight
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [hhalf]
      push_cast
      simp only [mem_insert, mem_singleton]
      right; right; left
      field_simp [show (6 * (h : ℚ) + 1) ≠ 0 by positivity]
      ring
    · rw [specialRoot_of_eq_six_mul_add_one hp7 hpform, hpform] at hrsum
      omega
  · obtain ⟨r, s, hrs, hf⟩ := card_eq_two.mp htwo
    have hr : r ∈ residueFiber p m := by simp [hf]
    have hs : s ∈ residueFiber p m := by simp [hf]
    have hrsum := distinct_fiber_roots_sum hp7 hr hs hrs
    rw [redundantCoeff_eq_fiber, hf,
      sum_insert (by simpa using hrs), sum_singleton]
    rw [hpform]
    have hhalf :
        (3 * (6 * (h : ℤ) + 1) - 1) / 2 = 9 * h + 1 := by omega
    unfold weight
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [hhalf]
    push_cast
    rcases hrsum with hrsum | hrsum
    · rw [specialRoot_of_eq_six_mul_add_one hp7 hpform] at hrsum
      simp only [mem_insert, mem_singleton]
      right; right; right
      have hrsumQ := congrArg (fun n : ℕ => (n : ℚ)) hrsum
      push_cast at hrsumQ
      field_simp [show (6 * (h : ℚ) + 1) ≠ 0 by positivity]
      linarith [hrsumQ]
    · rw [specialRoot_of_eq_six_mul_add_one hp7 hpform, hpform] at hrsum
      simp only [mem_insert, mem_singleton]
      left
      have hrsumQ := congrArg (fun n : ℕ => (n : ℚ)) hrsum
      push_cast at hrsumQ
      field_simp [show (6 * (h : ℚ) + 1) ≠ 0 by positivity]
      linarith [hrsumQ]

theorem cCoeff_T_mem_four_of_eq_six_mul_add_five (hp7 : 7 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) {h m : ℕ} (hpform : p = 6 * h + 5)
    (hm : m < p - 1) :
    cCoeff (K := ℚ) hζ m (T p ζ) ∈ ({0, 1, 2, 3} : Finset ℚ) := by
  rw [cCoeff_T_eq_redundant_sub hp7 hζ hm,
    redundantCoeff_pred_of_eq_six_mul_add_five hp7 hpform]
  have hcard := residueFiber_card_le_two hp7 m
  have hcases : #(residueFiber p m) = 0 ∨
      #(residueFiber p m) = 1 ∨ #(residueFiber p m) = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have hf : residueFiber p m = ∅ := card_eq_zero.mp hzero
    rw [redundantCoeff_eq_fiber, hf]
    norm_num
  · obtain ⟨r, hf⟩ := card_eq_one.mp hone
    have hrsum := singleton_fiber_root_sum hp7 hf
    rw [redundantCoeff_eq_fiber, hf, sum_singleton]
    rw [hpform]
    have hhalf :
        (3 * (6 * (h : ℤ) + 5) - 1) / 2 = 9 * h + 7 := by omega
    rcases hrsum with hrsum | hrsum
    · rw [specialRoot_of_eq_six_mul_add_five hp7 hpform] at hrsum
      omega
    · have hr : r = 5 * h + 4 := by
        rw [specialRoot_of_eq_six_mul_add_five hp7 hpform, hpform] at hrsum
        omega
      rw [hr]
      unfold weight
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [hhalf]
      push_cast
      simp only [mem_insert, mem_singleton]
      right; left
      field_simp [show (6 * (h : ℚ) + 5) ≠ 0 by positivity]
      ring
  · obtain ⟨r, s, hrs, hf⟩ := card_eq_two.mp htwo
    have hr : r ∈ residueFiber p m := by simp [hf]
    have hs : s ∈ residueFiber p m := by simp [hf]
    have hrsum := distinct_fiber_roots_sum hp7 hr hs hrs
    rw [redundantCoeff_eq_fiber, hf,
      sum_insert (by simpa using hrs), sum_singleton]
    rw [hpform]
    have hhalf :
        (3 * (6 * (h : ℤ) + 5) - 1) / 2 = 9 * h + 7 := by omega
    unfold weight
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [hhalf]
    push_cast
    rcases hrsum with hrsum | hrsum
    · rw [specialRoot_of_eq_six_mul_add_five hp7 hpform] at hrsum
      simp only [mem_insert, mem_singleton]
      right; right; right
      have hrsumQ := congrArg (fun n : ℕ => (n : ℚ)) hrsum
      push_cast at hrsumQ
      field_simp [show (6 * (h : ℚ) + 5) ≠ 0 by positivity]
      linarith [hrsumQ]
    · rw [specialRoot_of_eq_six_mul_add_five hp7 hpform, hpform] at hrsum
      simp only [mem_insert, mem_singleton]
      left
      have hrsumQ := congrArg (fun n : ℕ => (n : ℚ)) hrsum
      push_cast at hrsumQ
      field_simp [show (6 * (h : ℚ) + 5) ≠ 0 by positivity]
      linarith [hrsumQ]

theorem prime_eq_six_mul_add_one_or_five (hp7 : 7 ≤ p) :
    (∃ h, p = 6 * h + 1) ∨ ∃ h, p = 6 * h + 5 := by
  have hp : p.Prime := Fact.out
  have hrem_lt : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hdecomp : p = 6 * (p / 6) + p % 6 := by
    omega
  have heven (hr : p % 6 = 0 ∨ p % 6 = 2 ∨ p % 6 = 4) : False := by
    have hm := Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 6)
    rcases hr with hr | hr | hr <;> rw [hr] at hm <;> norm_num at hm
    all_goals
      have hd : 2 ∣ p := (Nat.dvd_iff_mod_eq_zero).mpr hm.symm
      rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  have hthree (hr : p % 6 = 3) : False := by
    have hm := Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 6)
    rw [hr] at hm
    norm_num at hm
    have hd : 3 ∣ p := (Nat.dvd_iff_mod_eq_zero).mpr hm.symm
    rcases (Nat.dvd_prime hp).mp hd with h | h <;> omega
  have hr : p % 6 = 1 ∨ p % 6 = 5 := by
    interval_cases hcase : p % 6
    · exact (heven (Or.inl rfl)).elim
    · exact Or.inl rfl
    · exact (heven (Or.inr (Or.inl rfl))).elim
    · exact (hthree rfl).elim
    · exact (heven (Or.inr (Or.inr rfl))).elim
    · exact Or.inr rfl
  rcases hr with hr | hr
  · left; exact ⟨p / 6, by omega⟩
  · right; exact ⟨p / 6, by omega⟩

/-- Every power-basis coefficient belongs to `{0,1,2,3}`. -/
theorem cCoeff_T_mem_four (hp7 : 7 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    {m : ℕ} (hm : m < p - 1) :
    cCoeff (K := ℚ) hζ m (T p ζ) ∈ ({0, 1, 2, 3} : Finset ℚ) := by
  rcases prime_eq_six_mul_add_one_or_five hp7 with ⟨h, hpform⟩ | ⟨h, hpform⟩
  · exact cCoeff_T_mem_four_of_eq_six_mul_add_one hp7 hζ hpform hm
  · exact cCoeff_T_mem_four_of_eq_six_mul_add_five hp7 hζ hpform hm

end MockTheta
