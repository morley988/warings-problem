import WaringSiegel.WSL3MomentThresholdSplicing

/-! # The optimized rational threshold gives actual integer minor moments -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson

theorem foldr_min_lt_witness (xs : List ℚ) (b p : ℚ) :
    xs.foldr min b < p → b<p ∨ ∃ a∈xs, a<p := by
  induction xs with
  | nil => intro h; exact Or.inl h
  | cons a xs ih =>
    intro h
    change min a (xs.foldr min b)<p at h
    rcases min_lt_iff.mp h with ha | hx
    · exact Or.inr ⟨a,by simp,ha⟩
    · rcases ih hx with hb | ⟨c,hc,hcp⟩
      · exact Or.inl hb
      · exact Or.inr ⟨c,List.mem_cons_of_mem a hc,hcp⟩

theorem second_threshold_ge_critical_of_order_ge (k : ℚ) (j : ℕ)
    (hj : (j:ℚ)≤k) (hm : k*(k+1)≤(2:ℚ)^j) :
    k*(k+1) ≤ Thresholds.second k j := by
  have hd : 0 < k+1-j := by linarith
  have he : Thresholds.second k j-k*(k+1) =
      ((2:ℚ)^j-k*(k+1))/(k+1-j) := by
    unfold Thresholds.second
    field_simp [hd.ne']
    <;> ring
  have hn := div_nonneg (sub_nonneg.mpr hm) hd.le
  linarith

theorem threshold_improving_witness (k p : ℕ) (hk : 3≤k) (hpT : p≤k*(k+1))
    (h : Thresholds.threshold k < (p:ℚ)) :
    (∃ r : ℕ, 1≤r ∧ r<k ∧ Thresholds.first (k:ℚ) r < (p:ℚ)) ∨
    (∃ j : ℕ, 1≤j ∧ j≤k ∧ 2^j<k*(k+1) ∧ Thresholds.second (k:ℚ) j < (p:ℚ)) := by
  have hpTQ : (p:ℚ)≤(k:ℚ)*(k+1) := by exact_mod_cast hpT
  obtain hbase | ⟨a,ha,hap⟩ := foldr_min_lt_witness (Thresholds.candidates k) ((k:ℚ)^2+1) p h
  · left
    refine ⟨1,by omega,by omega,?_⟩
    exact (Thresholds.first_one_lt_square (k:ℚ) (by exact_mod_cast (show 2<k by omega))).trans
      (by linarith)
  · rcases List.mem_append.mp ha with hfirst | hsecond
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hfirst
      have hrk : r+1≤k := by have := List.mem_range.mp hr; omega
      have hne : r+1≠k := by
        intro he
        rw [he] at hap
        have hid : Thresholds.first (k:ℚ) k=(k:ℚ)*(k+1) := by
          unfold Thresholds.first
          norm_num
          ring
        rw [hid] at hap
        linarith
      exact Or.inl ⟨r+1,by omega,by omega,hap⟩
    · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hsecond
      have hjk : j+1≤k := by have := List.mem_range.mp hj; omega
      have hm : 2^(j+1)<k*(k+1) := by
        by_contra hn
        have hge : k*(k+1)≤2^(j+1) := by omega
        have hb := second_threshold_ge_critical_of_order_ge (k:ℚ) (j+1)
          (by exact_mod_cast hjk) (by exact_mod_cast hge)
        linarith
      exact Or.inr ⟨j+1,by omega,hjk,hm,hap⟩

variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceWeylSum_threshold_minor_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k p : ℕ) (hk : 3≤k) (hpT : p≤k*(k+1))
    (hthreshold : Thresholds.threshold k < (p:ℚ)) :
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  rcases threshold_improving_witness k p hk hpT hthreshold with
    ⟨r,hr,hrk,hfirst⟩ | ⟨j,hj,hjk,hmT,hsecond⟩
  · exact compactTraceWeylSum_first_threshold_saving f hc k r p hk hr hrk hpT hfirst
  · exact compactTraceWeylSum_second_threshold_saving f hc k j p hk hj hjk hmT hpT hsecond

/-- The literal optimized variable threshold, up to the critical moment,
now has an actual positive outer-minor saving. -/
theorem compactTraceWeylSum_optimized_minor_saving_below_critical
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k p : ℕ) (hk : 3≤k) (hpT : p≤k*(k+1))
    (hvariables : Thresholds.sufficientVariables k ≤ (p:ℤ)) :
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  have ht : Thresholds.threshold k < (p:ℚ) := by
    apply (Thresholds.strict_floor_threshold_minimal (Thresholds.threshold k) (p:ℤ)).mp
    simpa only [Thresholds.sufficientVariables, if_neg (show k≠2 by omega)] using hvariables
  exact compactTraceWeylSum_threshold_minor_saving f hc k p hk hpT ht

#print axioms compactTraceWeylSum_optimized_minor_saving_below_critical
end WaringSiegel.WSL3
