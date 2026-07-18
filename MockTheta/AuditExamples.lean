import MockTheta.Corollaries

/-!
# Small-prime regression examples

These are typechecked examples, not the proof of the universal theorem.
-/

noncomputable section

namespace MockTheta

local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

example : specialRoot 7 = 2 := by
  exact specialRoot_of_eq_six_mul_add_one (p := 7) (by norm_num)
    (h := 1) (by norm_num)

example : specialRoot 11 = 7 := by
  exact specialRoot_of_eq_six_mul_add_five (p := 11) (by norm_num)
    (h := 1) (by norm_num)

example : specialRoot 13 = 4 := by
  exact specialRoot_of_eq_six_mul_add_one (p := 13) (by norm_num)
    (h := 2) (by norm_num)

example {L : Type*} [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {7} ℚ L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ 7) : c0 (K := ℚ) hζ (T 7 ζ) = 3 := by
  exact c0_T_eq_three (by norm_num) hζ

example {L : Type*} [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {11} ℚ L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ 11) : c0 (K := ℚ) hζ (T 11 ζ) = 3 := by
  exact c0_T_eq_three (by norm_num) hζ

example {L : Type*} [Field L] [Algebra ℚ L]
    [IsCyclotomicExtension {13} ℚ L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ 13) : c0 (K := ℚ) hζ (T 13 ζ) = 3 := by
  exact c0_T_eq_three (by norm_num) hζ

end MockTheta
