import WaringSiegel.WSL3MomentSplicingSaving
import WaringSiegel.Thresholds

/-! # Both manuscript threshold branches imply actual outer-minor saving -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson

theorem interpolation_weight_data {m p T : ℝ} (hmT : m<T) (hmp : m≤p) (hpT : p≤T) :
    0 ≤ (T-p)/(T-m) ∧ (T-p)/(T-m) ≤ 1 ∧
      p = m*((T-p)/(T-m))+T*(1-(T-p)/(T-m)) := by
  have hd : 0 < T-m := sub_pos.mpr hmT
  refine ⟨div_nonneg (sub_nonneg.mpr hpT) hd.le,
    (div_le_one hd).mpr (by linarith), ?_⟩
  field_simp [hd.ne']
  <;> ring

theorem first_threshold_ge_order {k r : ℚ} (hr : 0≤r) (hrk : r≤k) :
    r*(r+1) ≤ Thresholds.first k r := by
  have hk : 0 ≤ k := hr.trans hrk
  have hd : 0 < k-r+1 := by linarith
  have he : Thresholds.first k r-r*(r+1) = (k-r)^2*(k+r+1)/(k-r+1) := by
    unfold Thresholds.first
    field_simp [hd.ne']
    <;> ring
  have hn : 0 ≤ (k-r)^2*(k+r+1)/(k-r+1) := by positivity
  linarith

theorem second_saving_iff (k : ℚ) (j : ℕ) (p : ℚ)
    (hd : 0 < k*(k+1)-(2:ℚ)^j) (hj : 0 < k+1-j) :
    0 < 1-(k+1-j)*(k*(k+1)-p)/(k*(k+1)-(2:ℚ)^j) ↔ Thresholds.second k j < p := by
  unfold Thresholds.second
  rw [sub_pos, div_lt_one hd]
  have he : k^2-(k*j-(2:ℚ)^j)/(k+1-j) < p ↔
      k^2-p < (k*j-(2:ℚ)^j)/(k+1-j) := by
    constructor <;> intro h <;> linarith
  rw [he, lt_div_iff₀ hj]
  constructor <;> intro h <;> nlinarith

theorem second_threshold_ge_order (k : ℚ) (j : ℕ)
    (hj : (j:ℚ)≤k) (hm : (2:ℚ)^j≤k*(k+1)) :
    (2:ℚ)^j ≤ Thresholds.second k j := by
  have hd : 0 < k+1-j := by linarith
  have he : Thresholds.second k j-(2:ℚ)^j =
      (k*(k+1)-(2:ℚ)^j)*(k-j)/(k+1-j) := by
    unfold Thresholds.second
    field_simp [hd.ne']
    <;> ring
  have hdiff : 0 ≤ k*(k+1)-(2:ℚ)^j := sub_nonneg.mpr hm
  have hkj : 0 ≤ k-j := sub_nonneg.mpr hj
  have hn : 0 ≤ (k*(k+1)-(2:ℚ)^j)*(k-j)/(k+1-j) := by positivity
  linarith

variable {K : Type*} [Field K] [NumberField K]

/-- Strictly above the first rational threshold, the actual minor-arc
integral has a positive degree-independent volume saving. -/
theorem compactTraceWeylSum_first_threshold_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k r p : ℕ) (hk : 3 ≤ k) (hr : 1 ≤ r) (hrk : r<k)
    (hpT : p≤k*(k+1)) (hthreshold : Thresholds.first (k:ℚ) r < (p:ℚ)) :
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
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
  apply compactTraceWeylSum_generalized_hua_minor_saving f hc k r hk hr hrk.le p t ht0 ht1
  · simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using horder
  · simpa only [t,T,m,div_eq_mul_inv,mul_assoc] using hgainR

/-- The classical Hua branch is likewise an actual integral estimate. -/
theorem compactTraceWeylSum_second_threshold_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k j p : ℕ) (hk : 3 ≤ k) (hj : 1 ≤ j) (hjk : j≤k)
    (hmT : 2^j<k*(k+1)) (hpT : p≤k*(k+1))
    (hthreshold : Thresholds.second (k:ℚ) j < (p:ℚ)) :
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
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
  apply compactTraceWeylSum_classical_hua_minor_saving f hc k j hk hj hjk p t ht0 ht1
  · simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using horder
  · simpa only [t,T,m,div_eq_mul_inv,mul_assoc] using hgainR

#print axioms compactTraceWeylSum_first_threshold_saving
#print axioms compactTraceWeylSum_second_threshold_saving
end WaringSiegel.WSL3
