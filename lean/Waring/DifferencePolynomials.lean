import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Exact centered and ordinary difference polynomials

The five quadratic reductions used in the frozen degree-eight/nine policies
are proved by exact ring identities. The source normalization is the modified
forward difference in Vaughan--Wooley (2000), Section 2: a step of size
`2*h*m^k`, divided by `m^k`, applied to the translated kth power.

This module only proves polynomial identities, not bounds for their sums.
-/

noncomputable section
namespace Waring.Differences

def centeredPower (k : ℕ) : List ℝ → ℝ → ℝ
  | [], z => z ^ k
  | a :: rest, z => centeredPower k rest (z+a) - centeredPower k rest (z-a)

def forwardPower (k : ℕ) : List ℝ → ℝ → ℝ
  | [], z => z ^ k
  | a :: rest, z => forwardPower k rest (z+a) - forwardPower k rest z

/-- Centering is an identity in the polynomial definition, not a change in
the interval over which the auxiliary sum is taken. -/
theorem centered_eq_forward (k : ℕ) (shifts : List ℝ) (z : ℝ) :
    centeredPower k shifts z =
      forwardPower k (shifts.map (fun a => 2*a)) (z-shifts.sum) := by
  induction shifts generalizing z with
  | nil => simp [centeredPower, forwardPower]
  | cons a rest ih =>
    simp only [centeredPower, forwardPower, List.map_cons, List.sum_cons]
    rw [ih, ih]
    congr 1 <;> congr 1 <;> ring

def modifiedCenteredPower (k : ℕ) : List (ℝ × ℝ) → ℝ → ℝ
  | [], z => z ^ k
  | hm :: rest, z =>
    (modifiedCenteredPower k rest (z+hm.1*hm.2^k) -
      modifiedCenteredPower k rest (z-hm.1*hm.2^k)) / hm.2^k

/-- Normalization by the product of the coefficient powers. The identity
also holds at zero coefficients under Lean's totalized division convention. -/
theorem modifiedCenteredPower_eq (k : ℕ) (params : List (ℝ × ℝ)) (z : ℝ) :
    modifiedCenteredPower k params z =
      centeredPower k (params.map (fun hm => hm.1*hm.2^k)) z /
        (params.map (fun hm => hm.2^k)).prod := by
  induction params generalizing z with
  | nil => simp [modifiedCenteredPower, centeredPower]
  | cons hm rest ih =>
    simp only [modifiedCenteredPower, centeredPower, List.map_cons, List.prod_cons]
    rw [ih, ih, ← sub_div, div_div]
    rw [mul_comm (hm.2^k)]

def ordinaryDifference (f : ℝ → ℝ) (u z : ℝ) : ℝ := f (z+u) - f z

theorem cubic_to_quadratic (S C u z : ℝ) :
    ordinaryDifference (fun x => x^3/6+x*S/6+C) u z =
      u/24*(3*(2*z+u)^2+u^2+4*S) := by
  unfold ordinaryDifference
  ring

theorem quartic_to_quadratic (S C u v z : ℝ) :
    ordinaryDifference (ordinaryDifference (fun x => x^4/24+x^2*S/12+C) u) v z =
      u*v/24*(3*(2*z+u+v)^2+u^2+v^2+4*S) := by
  unfold ordinaryDifference
  ring

theorem centered8_1 (a1 z : ℝ) :
    centeredPower 8 [a1] z =
      16*a1*z^7 +
      112*a1^3*z^5 +
      112*a1^5*z^3 +
      16*a1^7*z := by

  simp only [centeredPower]
  ring

theorem centered8_2 (a1 a2 z : ℝ) :
    centeredPower 8 [a1, a2] z =
      224*a1*a2*z^6 +
      1120*a1*a2^3*z^4 +
      672*a1*a2^5*z^2 +
      32*a1*a2^7 +
      1120*a1^3*a2*z^4 +
      2240*a1^3*a2^3*z^2 +
      224*a1^3*a2^5 +
      672*a1^5*a2*z^2 +
      224*a1^5*a2^3 +
      32*a1^7*a2 := by

  change centeredPower 8 [a2] (z+a1) -
    centeredPower 8 [a2] (z-a1) = _
  rw [centered8_1, centered8_1]
  ring

theorem centered8_3 (a1 a2 a3 z : ℝ) :
    centeredPower 8 [a1, a2, a3] z =
      2688*a1*a2*a3*z^5 +
      8960*a1*a2*a3^3*z^3 +
      2688*a1*a2*a3^5*z +
      8960*a1*a2^3*a3*z^3 +
      8960*a1*a2^3*a3^3*z +
      2688*a1*a2^5*a3*z +
      8960*a1^3*a2*a3*z^3 +
      8960*a1^3*a2*a3^3*z +
      8960*a1^3*a2^3*a3*z +
      2688*a1^5*a2*a3*z := by

  change centeredPower 8 [a2, a3] (z+a1) -
    centeredPower 8 [a2, a3] (z-a1) = _
  rw [centered8_2, centered8_2]
  ring

theorem centered8_4 (a1 a2 a3 a4 z : ℝ) :
    centeredPower 8 [a1, a2, a3, a4] z =
      26880*a1*a2*a3*a4*z^4 +
      53760*a1*a2*a3*a4^3*z^2 +
      5376*a1*a2*a3*a4^5 +
      53760*a1*a2*a3^3*a4*z^2 +
      17920*a1*a2*a3^3*a4^3 +
      5376*a1*a2*a3^5*a4 +
      53760*a1*a2^3*a3*a4*z^2 +
      17920*a1*a2^3*a3*a4^3 +
      17920*a1*a2^3*a3^3*a4 +
      5376*a1*a2^5*a3*a4 +
      53760*a1^3*a2*a3*a4*z^2 +
      17920*a1^3*a2*a3*a4^3 +
      17920*a1^3*a2*a3^3*a4 +
      17920*a1^3*a2^3*a3*a4 +
      5376*a1^5*a2*a3*a4 := by

  change centeredPower 8 [a2, a3, a4] (z+a1) -
    centeredPower 8 [a2, a3, a4] (z-a1) = _
  rw [centered8_3, centered8_3]
  ring

theorem centered8_5 (a1 a2 a3 a4 a5 z : ℝ) :
    centeredPower 8 [a1, a2, a3, a4, a5] z =
      215040*a1*a2*a3*a4*a5*z^3 +
      215040*a1*a2*a3*a4*a5^3*z +
      215040*a1*a2*a3*a4^3*a5*z +
      215040*a1*a2*a3^3*a4*a5*z +
      215040*a1*a2^3*a3*a4*a5*z +
      215040*a1^3*a2*a3*a4*a5*z := by

  change centeredPower 8 [a2, a3, a4, a5] (z+a1) -
    centeredPower 8 [a2, a3, a4, a5] (z-a1) = _
  rw [centered8_4, centered8_4]
  ring

theorem centered8_6 (a1 a2 a3 a4 a5 a6 z : ℝ) :
    centeredPower 8 [a1, a2, a3, a4, a5, a6] z =
      1290240*a1*a2*a3*a4*a5*a6*z^2 +
      430080*a1*a2*a3*a4*a5*a6^3 +
      430080*a1*a2*a3*a4*a5^3*a6 +
      430080*a1*a2*a3*a4^3*a5*a6 +
      430080*a1*a2*a3^3*a4*a5*a6 +
      430080*a1*a2^3*a3*a4*a5*a6 +
      430080*a1^3*a2*a3*a4*a5*a6 := by

  change centeredPower 8 [a2, a3, a4, a5, a6] (z+a1) -
    centeredPower 8 [a2, a3, a4, a5, a6] (z-a1) = _
  rw [centered8_5, centered8_5]
  ring

theorem centered9_1 (a1 z : ℝ) :
    centeredPower 9 [a1] z =
      18*a1*z^8 +
      168*a1^3*z^6 +
      252*a1^5*z^4 +
      72*a1^7*z^2 +
      2*a1^9 := by

  simp only [centeredPower]
  ring

theorem centered9_2 (a1 a2 z : ℝ) :
    centeredPower 9 [a1, a2] z =
      288*a1*a2*z^7 +
      2016*a1*a2^3*z^5 +
      2016*a1*a2^5*z^3 +
      288*a1*a2^7*z +
      2016*a1^3*a2*z^5 +
      6720*a1^3*a2^3*z^3 +
      2016*a1^3*a2^5*z +
      2016*a1^5*a2*z^3 +
      2016*a1^5*a2^3*z +
      288*a1^7*a2*z := by

  change centeredPower 9 [a2] (z+a1) -
    centeredPower 9 [a2] (z-a1) = _
  rw [centered9_1, centered9_1]
  ring

theorem centered9_3 (a1 a2 a3 z : ℝ) :
    centeredPower 9 [a1, a2, a3] z =
      4032*a1*a2*a3*z^6 +
      20160*a1*a2*a3^3*z^4 +
      12096*a1*a2*a3^5*z^2 +
      576*a1*a2*a3^7 +
      20160*a1*a2^3*a3*z^4 +
      40320*a1*a2^3*a3^3*z^2 +
      4032*a1*a2^3*a3^5 +
      12096*a1*a2^5*a3*z^2 +
      4032*a1*a2^5*a3^3 +
      576*a1*a2^7*a3 +
      20160*a1^3*a2*a3*z^4 +
      40320*a1^3*a2*a3^3*z^2 +
      4032*a1^3*a2*a3^5 +
      40320*a1^3*a2^3*a3*z^2 +
      13440*a1^3*a2^3*a3^3 +
      4032*a1^3*a2^5*a3 +
      12096*a1^5*a2*a3*z^2 +
      4032*a1^5*a2*a3^3 +
      4032*a1^5*a2^3*a3 +
      576*a1^7*a2*a3 := by

  change centeredPower 9 [a2, a3] (z+a1) -
    centeredPower 9 [a2, a3] (z-a1) = _
  rw [centered9_2, centered9_2]
  ring

theorem centered9_4 (a1 a2 a3 a4 z : ℝ) :
    centeredPower 9 [a1, a2, a3, a4] z =
      48384*a1*a2*a3*a4*z^5 +
      161280*a1*a2*a3*a4^3*z^3 +
      48384*a1*a2*a3*a4^5*z +
      161280*a1*a2*a3^3*a4*z^3 +
      161280*a1*a2*a3^3*a4^3*z +
      48384*a1*a2*a3^5*a4*z +
      161280*a1*a2^3*a3*a4*z^3 +
      161280*a1*a2^3*a3*a4^3*z +
      161280*a1*a2^3*a3^3*a4*z +
      48384*a1*a2^5*a3*a4*z +
      161280*a1^3*a2*a3*a4*z^3 +
      161280*a1^3*a2*a3*a4^3*z +
      161280*a1^3*a2*a3^3*a4*z +
      161280*a1^3*a2^3*a3*a4*z +
      48384*a1^5*a2*a3*a4*z := by

  change centeredPower 9 [a2, a3, a4] (z+a1) -
    centeredPower 9 [a2, a3, a4] (z-a1) = _
  rw [centered9_3, centered9_3]
  ring

theorem centered9_5 (a1 a2 a3 a4 a5 z : ℝ) :
    centeredPower 9 [a1, a2, a3, a4, a5] z =
      483840*a1*a2*a3*a4*a5*z^4 +
      967680*a1*a2*a3*a4*a5^3*z^2 +
      96768*a1*a2*a3*a4*a5^5 +
      967680*a1*a2*a3*a4^3*a5*z^2 +
      322560*a1*a2*a3*a4^3*a5^3 +
      96768*a1*a2*a3*a4^5*a5 +
      967680*a1*a2*a3^3*a4*a5*z^2 +
      322560*a1*a2*a3^3*a4*a5^3 +
      322560*a1*a2*a3^3*a4^3*a5 +
      96768*a1*a2*a3^5*a4*a5 +
      967680*a1*a2^3*a3*a4*a5*z^2 +
      322560*a1*a2^3*a3*a4*a5^3 +
      322560*a1*a2^3*a3*a4^3*a5 +
      322560*a1*a2^3*a3^3*a4*a5 +
      96768*a1*a2^5*a3*a4*a5 +
      967680*a1^3*a2*a3*a4*a5*z^2 +
      322560*a1^3*a2*a3*a4*a5^3 +
      322560*a1^3*a2*a3*a4^3*a5 +
      322560*a1^3*a2*a3^3*a4*a5 +
      322560*a1^3*a2^3*a3*a4*a5 +
      96768*a1^5*a2*a3*a4*a5 := by

  change centeredPower 9 [a2, a3, a4, a5] (z+a1) -
    centeredPower 9 [a2, a3, a4, a5] (z-a1) = _
  rw [centered9_4, centered9_4]
  ring

theorem centered9_6 (a1 a2 a3 a4 a5 a6 z : ℝ) :
    centeredPower 9 [a1, a2, a3, a4, a5, a6] z =
      3870720*a1*a2*a3*a4*a5*a6*z^3 +
      3870720*a1*a2*a3*a4*a5*a6^3*z +
      3870720*a1*a2*a3*a4*a5^3*a6*z +
      3870720*a1*a2*a3*a4^3*a5*a6*z +
      3870720*a1*a2*a3^3*a4*a5*a6*z +
      3870720*a1*a2^3*a3*a4*a5*a6*z +
      3870720*a1^3*a2*a3*a4*a5*a6*z := by

  change centeredPower 9 [a2, a3, a4, a5, a6] (z+a1) -
    centeredPower 9 [a2, a3, a4, a5, a6] (z-a1) = _
  rw [centered9_5, centered9_5]
  ring

theorem quadratic_reduction_k8_j4 (h1 m1 h2 m2 h3 m3 h4 m4 u v z : ℝ)
    (hm1 : m1 ≠ 0)
    (hm2 : m2 ≠ 0)
    (hm3 : m3 ≠ 0)
    (hm4 : m4 ≠ 0) :
    (ordinaryDifference (ordinaryDifference (modifiedCenteredPower 8 [(h1,m1), (h2,m2), (h3,m3), (h4,m4)]) u) v) z =
      (645120/24)*(h1*h2*h3*h4*u*v)*(3*(2*z+u+v)^2+u^2+v^2+4*(h1^2*m1^16+h2^2*m2^16+h3^2*m3^16+h4^2*m4^16)) := by

  simp only [ordinaryDifference, modifiedCenteredPower_eq, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

  simp only [centered8_4]

  field_simp
  ring

theorem quadratic_reduction_k8_j5 (h1 m1 h2 m2 h3 m3 h4 m4 h5 m5 u z : ℝ)
    (hm1 : m1 ≠ 0)
    (hm2 : m2 ≠ 0)
    (hm3 : m3 ≠ 0)
    (hm4 : m4 ≠ 0)
    (hm5 : m5 ≠ 0) :
    (ordinaryDifference (modifiedCenteredPower 8 [(h1,m1), (h2,m2), (h3,m3), (h4,m4), (h5,m5)]) u) z =
      (1290240/24)*(h1*h2*h3*h4*h5*u)*(3*(2*z+u)^2+u^2+4*(h1^2*m1^16+h2^2*m2^16+h3^2*m3^16+h4^2*m4^16+h5^2*m5^16)) := by

  simp only [ordinaryDifference, modifiedCenteredPower_eq, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

  simp only [centered8_5]

  field_simp
  ring

theorem quadratic_reduction_k8_j6 (h1 m1 h2 m2 h3 m3 h4 m4 h5 m5 h6 m6  z : ℝ)
    (hm1 : m1 ≠ 0)
    (hm2 : m2 ≠ 0)
    (hm3 : m3 ≠ 0)
    (hm4 : m4 ≠ 0)
    (hm5 : m5 ≠ 0)
    (hm6 : m6 ≠ 0) :
    (modifiedCenteredPower 8 [(h1,m1), (h2,m2), (h3,m3), (h4,m4), (h5,m5), (h6,m6)]) z =
      (2580480/24)*(h1*h2*h3*h4*h5*h6)*(3*(2*z)^2+4*(h1^2*m1^16+h2^2*m2^16+h3^2*m3^16+h4^2*m4^16+h5^2*m5^16+h6^2*m6^16)) := by

  simp only [modifiedCenteredPower_eq, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

  simp only [centered8_6]

  field_simp
  ring

theorem quadratic_reduction_k9_j5 (h1 m1 h2 m2 h3 m3 h4 m4 h5 m5 u v z : ℝ)
    (hm1 : m1 ≠ 0)
    (hm2 : m2 ≠ 0)
    (hm3 : m3 ≠ 0)
    (hm4 : m4 ≠ 0)
    (hm5 : m5 ≠ 0) :
    (ordinaryDifference (ordinaryDifference (modifiedCenteredPower 9 [(h1,m1), (h2,m2), (h3,m3), (h4,m4), (h5,m5)]) u) v) z =
      (11612160/24)*(h1*h2*h3*h4*h5*u*v)*(3*(2*z+u+v)^2+u^2+v^2+4*(h1^2*m1^18+h2^2*m2^18+h3^2*m3^18+h4^2*m4^18+h5^2*m5^18)) := by

  simp only [ordinaryDifference, modifiedCenteredPower_eq, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

  simp only [centered9_5]

  field_simp
  ring

theorem quadratic_reduction_k9_j6 (h1 m1 h2 m2 h3 m3 h4 m4 h5 m5 h6 m6 u z : ℝ)
    (hm1 : m1 ≠ 0)
    (hm2 : m2 ≠ 0)
    (hm3 : m3 ≠ 0)
    (hm4 : m4 ≠ 0)
    (hm5 : m5 ≠ 0)
    (hm6 : m6 ≠ 0) :
    (ordinaryDifference (modifiedCenteredPower 9 [(h1,m1), (h2,m2), (h3,m3), (h4,m4), (h5,m5), (h6,m6)]) u) z =
      (23224320/24)*(h1*h2*h3*h4*h5*h6*u)*(3*(2*z+u)^2+u^2+4*(h1^2*m1^18+h2^2*m2^18+h3^2*m3^18+h4^2*m4^18+h5^2*m5^18+h6^2*m6^18)) := by

  simp only [ordinaryDifference, modifiedCenteredPower_eq, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

  simp only [centered9_6]

  field_simp
  ring

end Waring.Differences
