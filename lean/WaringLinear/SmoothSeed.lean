import Waring.SeedCompletionGenericEndpoint
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # An unconditional smooth mean-value seed in every degree

At half-order n+2 the first shortening step gives a geometric normalized
defect. Rounding the logarithmic inverse provides a genuine smooth moment
with the prescribed defect and its usual cutoff uniformity.
-/
noncomputable section
namespace WaringLinear
open Waring.SmoothMoments Waring.SeedCompletionGenericEndpoint

theorem geometric_defect (k n : ℕ) (hk : 2≤k) :
    (offsetExponent k n : ℝ) =
      2*((n:ℝ)+2)-k+((k:ℝ)-2)*(1-1/(k:ℝ))^n := by
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  induction n with
  | zero => simp [offsetExponent];ring
  | succ n ih =>
    rw [offsetExponent,Rat.cast_add,Rat.cast_add,Rat.cast_div,Rat.cast_sub,Rat.cast_mul]
    push_cast
    rw [ih,pow_succ]
    field_simp
    ring

/-- Uniform in all cutoffs below the power supplied by the error parameter. -/
theorem geometric_smooth_seed (k : ℕ) (D : ℝ) (hk : 2≤k) (hD : 0<D) :
    AdmissibleExcess k (2*(⌈-(k:ℝ)*Real.log D⌉₊+2)) ((k:ℝ)*D) := by
  let n := ⌈-(k:ℝ)*Real.log D⌉₊
  have hk' : (2:ℝ)≤k := by exact_mod_cast hk
  have hkp : (0:ℝ)<k := by linarith
  have hr : 0≤1-1/(k:ℝ) := sub_nonneg.mpr ((div_le_one hkp).2 (by linarith))
  have h₁ : 1-1/(k:ℝ)≤Real.exp (-(1/(k:ℝ))) := by linarith only [Real.add_one_le_exp (-(1/(k:ℝ)))]
  have hpow := pow_le_pow_left₀ hr h₁ n
  rw [←Real.exp_nat_mul] at hpow
  have hc : -(k:ℝ)*Real.log D≤n := Nat.le_ceil _
  have he : (n:ℝ)*(-(1/(k:ℝ)))≤Real.log D := by
    apply (le_of_mul_le_mul_right _ hkp)
    calc
      (n:ℝ)*(-(1/(k:ℝ)))*k = -n := by field_simp
      _ ≤ Real.log D*k := by linarith only [hc]
  have hdr : (1-1/(k:ℝ))^n≤D :=
    hpow.trans ((Real.exp_le_exp.mpr he).trans_eq (Real.exp_log hD))
  have hscale := mul_le_mul_of_nonneg_left hdr (by linarith : 0≤(k:ℝ)-2)
  apply admissibleExponent_mono (offsetExponent_admissible hk n)
  rw [geometric_defect k n hk]
  change _ ≤ ((2*(n+2):ℕ):ℝ)-k+k*D
  push_cast
  nlinarith only [hscale,hD]

#print axioms geometric_smooth_seed
end WaringLinear
