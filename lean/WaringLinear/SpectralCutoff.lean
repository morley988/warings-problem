import WaringLinear.TruncatedSpectrum
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Semiring

/-! # Dyadic truncation at a real Fourier amplitude -/
noncomputable section
open scoped BigOperators Classical
namespace WaringLinear

/-- The ceiling of the base-two logarithm of the inverse relative
amplitude changes the threshold by at most a factor of two. -/
theorem spectral_cutoff_exists (X Y : ℝ) (hY : 0<Y) (hYX : Y≤X) :
    ∃ J : ℕ, (J:ℝ) < Real.logb 2 (X/Y)+1 ∧
      Y/2 < X/(2:ℝ)^J ∧ X/(2:ℝ)^J≤Y := by
  let b := Real.logb 2 (X/Y)
  let J := ⌈b⌉₊
  have hX : 0<X := hY.trans_le hYX
  have hratio : 0<X/Y := div_pos hX hY
  have h1 : (1:ℝ)≤X/Y := (one_le_div hY).mpr hYX
  have hb : 0≤b := Real.logb_nonneg (by norm_num) h1
  have blo : b≤J := Nat.le_ceil b
  have bhi : (J:ℝ)<b+1 := Nat.ceil_lt_add_one hb
  have plo : X/Y≤(2:ℝ)^J := by
    simpa only [Real.rpow_natCast] using
      (Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ)<2) hratio).mp blo
  have phi : (2:ℝ)^J < X/Y*2 := by
    have H := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) bhi
    simpa only [Real.rpow_natCast,Real.rpow_add (by norm_num : (0:ℝ)<2),
      Real.rpow_one,b,Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) hratio] using H
  have hj : 0<(2:ℝ)^J := by positivity
  refine ⟨J,bhi,(lt_div_iff₀ hj).2 ?_,(div_le_iff₀ hj).2 ?_⟩
  · rw [div_mul_eq_mul_div,(lt_div_iff₀ hY)] at phi
    linarith only [phi]
  · rw [div_le_iff₀ hY] at plo
    simpa only [mul_comm] using plo

/-- Conversion between an indicator at any real cutoff and the finite
dyadic spectrum. No logarithmic or cardinality factor occurs here. -/
theorem indicator_sum_le_spectrum {ι : Type*} [Fintype ι] (u : ι→ℝ) (X Y : ℝ)
    (hX : 0<X) (J : ℕ) (hc : X/(2:ℝ)^J≤Y) :
    (∑i, {v : ℝ | Y≤v}.indicator (fun v => v^2) (u i)) ≤
      ∑i∈spectrum (fun i => u i/X) J,(u i)^2 := by
  classical
  rw [spectrum,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : Y≤u i
  · have jpos : 0<(2:ℝ)^J := by positivity
    have w := (div_le_iff₀ jpos).mp (hc.trans h)
    have hw : 1≤(2:ℝ)^J*(u i/X) := by
      rw [←mul_div_assoc,one_le_div hX]
      simpa only [mul_comm] using w
    simp [Set.indicator_of_mem,h,hw]
  · simp only [Set.indicator_of_notMem (show u i∉{v : ℝ | Y≤v} from h)]
    split <;> positivity

#print axioms spectral_cutoff_exists
#print axioms indicator_sum_le_spectrum
end WaringLinear
