import WaringSiegel.WSL4MajorFlexibleSaving
import WaringSiegel.WSL3MomentOptimizedMinor
import WaringSiegel.Thresholds

/-! # Both manuscript threshold branches imply a smaller-cutoff minor saving -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson

variable {K : Type*} [Field K] [NumberField K]

/-- Strictly above the first rational threshold, the actual minor-arc
integral has a positive degree-independent volume saving. -/
theorem compactTraceWeylSum_first_threshold_shrinking_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k r p : ℕ) (hk : 3 ≤ k) (hr : 1 ≤ r) (hrk : r<k)
    (hpT : p≤k*(k+1)) (hthreshold : Thresholds.first (k:ℚ) r < (p:ℚ)) :
    ∃ a C η : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in shrinkingMinorArcs (K := K) k a P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  have hrQ : (r:ℚ)<k := by exact_mod_cast hrk
  have hdQ : 0 < (k:ℚ)*(k+1)-(r:ℚ)*(r+1) := by
    have hprod := mul_pos (sub_pos.mpr hrQ)
      (show 0 < (k:ℚ)+r+1 by nlinarith [Nat.cast_nonneg (α:=ℚ) r])
    nlinarith
  have hkrQ : 0 < (k:ℚ)-r+1 := by linarith
  have hmpQ := lt_of_le_of_lt (first_threshold_ge_order (Nat.cast_nonneg r) hrQ.le) hthreshold
  have hmp : (r*(r+1):ℕ) ≤ p := by exact_mod_cast hmpQ.le
  let T : ℝ := (k:ℝ)*(k+1)
  let m : ℝ := (r:ℝ)*(r+1)
  let t : ℝ := (T-p)/(T-m)
  have hmT : m<T := by
    dsimp [m,T]
    exact_mod_cast (sub_pos.mp hdQ)
  have hmpR : m≤(p:ℝ) := by dsimp [m]; exact_mod_cast hmp
  have hpTR : (p:ℝ)≤T := by dsimp [T]; exact_mod_cast hpT
  obtain ⟨ht0,ht1,horder⟩ := interpolation_weight_data hmT hmpR hpTR
  have hgainQ := (Thresholds.first_saving_iff (k:ℚ) r p hdQ hkrQ).mpr hthreshold
  have hgainR : 0 < 1-((k:ℝ)-r+1)*((k:ℝ)*(k+1)-p)/
      ((k:ℝ)*(k+1)-(r:ℝ)*(r+1)) := by exact_mod_cast hgainQ
  apply compactTraceWeylSum_generalized_hua_shrinking_saving f hc k r hk hr hrk.le p t ht0 ht1
  · simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using horder
  · simpa only [t,T,m,div_eq_mul_inv,mul_assoc] using hgainR

/-- The classical Hua branch is likewise an actual integral estimate. -/
theorem compactTraceWeylSum_second_threshold_shrinking_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k j p : ℕ) (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : j≤k)
    (hmT : 2^j<k*(k+1)) (hpT : p≤k*(k+1))
    (hthreshold : Thresholds.second (k:ℚ) j < (p:ℚ)) :
    ∃ a C η : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in shrinkingMinorArcs (K := K) k a P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  have hjQ : (j:ℚ)≤k := by exact_mod_cast hjk
  have hmQ : (2:ℚ)^j < (k:ℚ)*(k+1) := by exact_mod_cast hmT
  have hdQ : 0 < (k:ℚ)*(k+1)-(2:ℚ)^j := sub_pos.mpr hmQ
  have hdenQ : 0 < (k:ℚ)+1-j := by linarith
  have hmpQ := lt_of_le_of_lt (second_threshold_ge_order (k:ℚ) j hjQ hmQ.le) hthreshold
  have hmp : (2:ℕ)^j≤p := by exact_mod_cast hmpQ.le
  let T : ℝ := (k:ℝ)*(k+1)
  let m : ℝ := (2:ℝ)^j
  let t : ℝ := (T-p)/(T-m)
  have hmTR : m<T := by dsimp [m,T]; exact_mod_cast hmT
  have hmpR : m≤(p:ℝ) := by dsimp [m]; exact_mod_cast hmp
  have hpTR : (p:ℝ)≤T := by dsimp [T]; exact_mod_cast hpT
  obtain ⟨ht0,ht1,horder⟩ := interpolation_weight_data hmTR hmpR hpTR
  have hgainQ := (second_saving_iff (k:ℚ) j p hdQ hdenQ).mpr hthreshold
  have hgainR : 0 < 1-((k:ℝ)+1-j)*((k:ℝ)*(k+1)-p)/
      ((k:ℝ)*(k+1)-(2:ℝ)^j) := by exact_mod_cast hgainQ
  apply compactTraceWeylSum_classical_hua_shrinking_saving f hc k j hk hj hjk p t ht0 ht1
  · simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using horder
  · simpa only [t,T,m,div_eq_mul_inv,mul_assoc] using hgainR

#print axioms compactTraceWeylSum_first_threshold_shrinking_saving
#print axioms compactTraceWeylSum_second_threshold_shrinking_saving
end WaringSiegel.WSL4
