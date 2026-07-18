import MockTheta.ConstantCoordinate
import MockTheta.FineCollapse

/-!
# The constant-coordinate theorem

This file joins the finite Fine collapse to the independently proved
reverse-Fine coordinate calculation.
-/

noncomputable section

namespace MockTheta

variable {p : ℕ} [Fact p.Prime]
variable {L : Type*} [Field L] [Algebra ℚ L]
variable [IsCyclotomicExtension {p} ℚ L]
variable {ζ : L}

/-- The exact weighted formula for the original mock-theta value. -/
theorem weighted_formula (hp7 : 7 ≤ p) (hζ : IsPrimitiveRoot ζ p) :
    T p ζ =
      (p : L)⁻¹ *
        ∑ n ∈ Finset.range p,
          (((weight p n : ℤ) : L)) * (ζ⁻¹) ^ quadraticExp n := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  letI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  rw [reverseFine hodd hp.pos hζ,
    weighted_formula_reverse hodd hp.pos hζ.inv]

/-- For every prime `p ≥ 7`, the constant power-basis coordinate of the
root-of-unity value `T p ζ` is `3`. -/
theorem c0_T_eq_three (hp7 : 7 ≤ p) (hζ : IsPrimitiveRoot ζ p) :
    c0 (K := ℚ) hζ (T p ζ) = 3 := by
  have hp : p.Prime := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  letI : CharZero L :=
    charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  rw [reverseFine hodd hp.pos hζ]
  exact c0_reverseFine_eq_three hp7 hζ

/-- Directive-compatible public name for `c0_T_eq_three`. -/
theorem constantCoeff_T_eq_three (hp7 : 7 ≤ p)
    (hζ : IsPrimitiveRoot ζ p) :
    c0 (K := ℚ) hζ (T p ζ) = 3 :=
  c0_T_eq_three hp7 hζ

end MockTheta
