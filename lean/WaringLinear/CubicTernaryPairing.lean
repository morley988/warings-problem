import Mathlib.Tactic

/-! Exact identities used in the seven-cube construction. All are
polynomial identities over a commutative ring, except for the final
cancellation in the assembled representation and the residue identities. -/

namespace WaringLinear.CubicTernaryPairing

variable {R : Type*} [CommRing R]

def ternary (x y z : R) : R := 16*x^2+4*x*y+3*y^2+32*z^2

def centerSum (u v w : R) : R :=
  u^6*v^6+11^3*u^6*w^6+8^3*v^6*w^6

theorem four_ternary (x y z : R) :
    4*ternary x y z = (8*x+y)^2+11*y^2+8*(4*z)^2 := by
  unfold ternary
  ring

theorem cube_pair (m h : R) : (m+h)^3+(m-h)^3 = 2*m^3+6*m*h^2 := by
  ring

/-- The six roots are initially doubled so the identity also applies to
integral constructions where division by two is unavailable. -/
theorem six_doubled_cubes (u v w s x y z : R) :
    (u^2*v^2*s+w*(8*x+y))^3 + (u^2*v^2*s-w*(8*x+y))^3 +
    ((11*u^2*w^2*s+v*y)^3 + (11*u^2*w^2*s-v*y)^3) +
    ((8*v^2*w^2*s+u*(4*z))^3 + (8*v^2*w^2*s-u*(4*z))^3) =
      2*s^3*centerSum u v w + 24*s*(u^2*v^2*w^2)*ternary x y z := by
  rw [cube_pair, cube_pair, cube_pair]
  unfold ternary centerSum
  ring

/-- Recover the actual seven-cube equality from an integral ternary
representation and the six parity-compatible roots. -/
theorem seven_cubes_of_ternary [IsDomain R] [CharZero R]
    (u v w s x y z t target a b c d e f : R)
    (ha : 2*a = u^2*v^2*s+w*(8*x+y)) (hb : 2*b = u^2*v^2*s-w*(8*x+y))
    (hc : 2*c = 11*u^2*w^2*s+v*y) (hd : 2*d = 11*u^2*w^2*s-v*y)
    (he : 2*e = 8*v^2*w^2*s+u*(4*z)) (hf : 2*f = 8*v^2*w^2*s-u*(4*z))
    (htarget : 4*(target-t^3) = s^3*centerSum u v w +
      12*s*(u^2*v^2*w^2)*ternary x y z) :
    a^3+b^3+c^3+d^3+e^3+f^3+t^3 = target := by
  have h := six_doubled_cubes u v w s x y z
  rw [← ha, ← hb, ← hc, ← hd, ← he, ← hf] at h
  apply mul_left_cancel₀ (show (8 : R) ≠ 0 by norm_num)
  linear_combination h - 2*htarget

/-- The integral polynomial prescribing the dyadic target. -/
def dyadicPoly (D : R) : R :=
  29488*D^6 + 88464*D^5 + 110580*D^4 + 73720*D^3 + 27681*D^2 + 5565*D + 470

theorem four_dyadicPoly (D : R) :
    4*dyadicPoly D = centerSum 1 1 (1+2*D) + 36*(1+2*D)^2 := by
  unfold dyadicPoly centerSum
  ring

theorem dyadicPoly_mod_two [CharP R 2] (D : R) : dyadicPoly D = D^2+D := by
  unfold dyadicPoly
  have h : (2 : R) = 0 := CharP.cast_eq_zero R 2
  linear_combination (14744*D^6+44232*D^5+55290*D^4+36860*D^3+13840*D^2+2782*D+235)*h

/-- In characteristic two, three cubes can impose an Artin--Schreier
condition, including in rings with nilpotents. -/
theorem three_cube_residue [CharP R 2] (x z : R) :
    z^3+x^3+(x+1)^3 = z^3+x^2+x+1 := by
  have h : (2 : R) = 0 := CharP.cast_eq_zero R 2
  linear_combination (x^3+x^2+x)*h

theorem center_mod_three [CharP R 3] (u v w : R) :
    centerSum u v w = (u^2*v^2+11*u^2*w^2+8*v^2*w^2)^3 := by
  rw [add_pow_char, add_pow_char]
  unfold centerSum
  ring

theorem four_signed_cubes (y : R) :
    (y+1)^3+(y-1)^3+(-y)^3+(-y)^3 = 6*y := by ring

/-- A cube root of two condenses the linear residual into three cubes. -/
theorem three_signed_cubes_of_cube_root_two (β y : R) (hβ : β^3 = 2) :
    (y+1)^3+(y-1)^3+(-β*y)^3 = 6*y := by
  rw [mul_pow]
  linear_combination -y^3*hβ

#print axioms seven_cubes_of_ternary
#print axioms four_dyadicPoly
#print axioms three_cube_residue
#print axioms three_signed_cubes_of_cube_root_two

end WaringLinear.CubicTernaryPairing
