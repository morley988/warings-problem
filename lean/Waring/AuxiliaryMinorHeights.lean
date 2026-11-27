import Waring.AuxiliaryMajorArcs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The actual normalized height on the original auxiliary minor arcs

The height coordinate is defined from the actual intrinsic height. The source
cutoff retains both the R power and a fixed conductor factor. Their small
losses appear explicitly in the lower endpoint; the upper endpoint follows
from Dirichlet approximation for the normalized conductor.
-/

noncomputable section
namespace Waring.AuxiliaryMinorHeights
open RationalHeight BasicMatching

def normalizedHeight (P V α : ℝ) : ℝ := Real.log (height V α)/Real.log P

theorem height_eq_normalized {P : ℝ} (hP : 1 < P) (V α : ℝ) :
    P^(normalizedHeight P V α) = height V α := by
  have hPp : 0 < P := zero_lt_one.trans hP
  have hlog : Real.log P ≠ 0 := (Real.log_pos hP).ne'
  rw [Real.rpow_def_of_pos hPp]
  unfold normalizedHeight
  have heq : Real.log P*(Real.log (height V α)/Real.log P)=Real.log (height V α) := by
    field_simp
  rw [heq,Real.exp_log (height_pos V α)]

theorem measurable_normalizedHeight (P : ℝ) {V : ℝ} (hV : 0 < V) :
    Measurable (normalizedHeight P V) := by
  unfold normalizedHeight
  exact (measurable_height hV).log.div_const _

/-- The original minor cutoff gives this exact lower bound, including every
fixed conductor factor and positive smoothness power. -/
theorem minor_height_lower_scaled {P V R rho c α : ℝ}
    (hP : 0 < P) (hV : 0 < V) (hR : 1 ≤ R) (hrho : 0 ≤ rho) (hc : 1 ≤ c)
    (hminor : MinorAtCutoff P ((c*V/P)*R^rho) α) :
    P/(c*R^rho) < height V α := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hcp : 0 < c := zero_lt_one.trans_le hc
  have hX : 0 < (c*V/P)*R^rho := by positivity
  have hh := minor_height_lower hminor hX hV
  have hcancel : V/((c*V/P)*R^rho)=P/(c*R^rho) := by field_simp
  have hden : 1 ≤ c*R^rho := by
    have hh := mul_le_mul hc (Real.one_le_rpow hR hrho)
      (by norm_num : (0:ℝ) ≤ 1) hcp.le
    simpa only [one_mul] using hh
  have hfrac : P/(c*R^rho) ≤ P := div_le_self hP.le hden
  simpa only [hcancel,min_eq_right hfrac] using hh

/-- The literal normalized conductor has no hidden fixed-factor upper-height
loss. Any fixed factor in the original arc cutoff is charged to delta. -/
theorem minor_normalized_bounds {P R v rho η δ c α : ℝ}
    (hP : 1 < P) (hR : 1 ≤ R) (hRup : R ≤ P^η)
    (hv : 0 ≤ v) (hrho : 0 ≤ rho) (hc : 1 ≤ c) (hcP : c ≤ P^δ)
    (hminor : MinorAtCutoff P ((c*P^v/P)*R^rho) α) :
    1-rho*η-δ < normalizedHeight P (P^v) α ∧
      normalizedHeight P (P^v) α ≤ v/2 := by
  have hPp : 0 < P := zero_lt_one.trans hP
  have hVp : 0 < P^v := Real.rpow_pos_of_pos hPp _
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hcp : 0 < c := zero_lt_one.trans_le hc
  have hdenpos : 0 < c*R^rho := by positivity
  have hRpow : R^rho ≤ P^(η*rho) := by
    rw [Real.rpow_mul hPp.le]
    exact Real.rpow_le_rpow hRp.le hRup hrho
  have hden : c*R^rho ≤ P^(δ+η*rho) := by
    rw [Real.rpow_add hPp]
    exact mul_le_mul hcP hRpow (Real.rpow_nonneg hRp.le _) (Real.rpow_nonneg hPp.le _)
  have hlow := minor_height_lower_scaled hPp hVp hR hrho hc hminor
  have hpow : P^(1-rho*η-δ) ≤ P/(c*R^rho) := by
    calc
      _ = P/P^(δ+η*rho) := by
        have he : 1-rho*η-δ = 1-(δ+η*rho) := by ring
        rw [he,Real.rpow_sub hPp,Real.rpow_one]
      _ ≤ _ := div_le_div_of_nonneg_left hPp.le hdenpos hden
  have hheight := height_eq_normalized hP (P^v) α
  constructor
  · apply (Real.rpow_lt_rpow_left_iff hP).mp
    rw [hheight]
    exact hpow.trans_lt hlow
  · apply (Real.rpow_le_rpow_left_iff hP).mp
    rw [hheight]
    calc
      _ ≤ Real.sqrt (P^v) := height_le_sqrt (Real.one_le_rpow hP.le hv) α
      _ = P^(v/2) := by
        rw [Real.sqrt_eq_rpow,← Real.rpow_mul hPp.le]
        congr 1
        ring

#print axioms height_eq_normalized
#print axioms minor_normalized_bounds
end Waring.AuxiliaryMinorHeights
