import WaringSiegel.WSL4MajorFlexibleAll
import WaringSiegel.WSL4MajorSources
import WaringSiegel.WSL3MomentRepresentationEndgame

/-! # Actual broad-minus-narrow pruning from the smaller-cutoff moment -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem traceMajorArcUnion_mono_cutoff (H L M : ℝ) (hLM : L≤M) :
    traceMajorArcUnion (K := K) H L ⊆ traceMajorArcUnion H M := by
  intro q hq
  obtain ⟨γ,hγ⟩ := Set.mem_iUnion.mp hq
  obtain ⟨x,hx,hxq⟩ := hγ
  exact Set.mem_iUnion.mpr ⟨γ,x,le_trans hx hLM,hxq⟩

theorem compactTraceWeylSum_shrinking_pruning
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k p : ℕ) (hk : 3≤k) (hvariables : Thresholds.sufficientVariables k≤(p:ℤ)) :
    ∃ a C η : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P), ∀ target : 𝓞 K,
      ‖(∫ q in traceMajorArcUnion (P^k) ((k:ℝ)^finrank ℚ K*P^finrank ℚ K),
          compactTraceWeylSum k f hc P (by linarith) q^p * traceTorusCharacter (-target) q ∂traceHaar)-
        (∫ q in traceMajorArcUnion (P^k) ((k:ℝ)^finrank ℚ K*(P^finrank ℚ K)^a),
          compactTraceWeylSum k f hc P (by linarith) q^p * traceTorusCharacter (-target) q ∂traceHaar)‖ ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  obtain ⟨a,C,η,ha0,ha1,hC,hη,hminor⟩ :=
    compactTraceWeylSum_optimized_shrinking_saving f hc k p hk hvariables
  refine ⟨a,C,η,ha0,ha1,hC,hη,?_⟩
  intro P hP target
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  let X := P^finrank ℚ K
  have hX : 1≤X := one_le_pow₀ hP
  let A := traceMajorArcUnion (K := K) (P^k) ((k:ℝ)^finrank ℚ K*X^a)
  let B := traceMajorArcUnion (K := K) (P^k) ((k:ℝ)^finrank ℚ K*X)
  let g : ArchimedeanTraceTorus K → ℂ := fun q =>
    compactTraceWeylSum k f hc P hP0.ne' q^p * traceTorusCharacter (-target) q
  have hg : Continuous g := ((compactTraceWeylSum_continuous _ _ _ _ _).pow p).mul
    (traceTorusCharacter_continuous _)
  have hig : Integrable g traceHaar := hg.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hA : MeasurableSet A := traceMajorArcUnion_measurableSet _ _ (pow_pos hP0 k)
  have hAB : A⊆B := by
    apply traceMajorArcUnion_mono_cutoff
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX ha1.le
  have hnorm (q : ArchimedeanTraceTorus K) :
      ‖g q‖=‖compactTraceWeylSum k f hc P hP0.ne' q‖^p := by
    simp only [g,norm_mul,norm_pow,traceTorusCharacter,norm_latticeCharacter_eq_one,mul_one]
  change ‖(∫ q in B,g q ∂traceHaar)-(∫ q in A,g q ∂traceHaar)‖≤_
  rw [← integral_diff hA hig.integrableOn hAB]
  apply (norm_integral_le_integral_norm _).trans
  have hsub : (∫ q in B\A,‖g q‖ ∂traceHaar)≤∫ q in Aᶜ,‖g q‖ ∂traceHaar :=
    setIntegral_mono_set hig.norm.integrableOn (Filter.Eventually.of_forall (fun q => norm_nonneg _))
      (Filter.Eventually.of_forall (fun q hq => hq.2))
  apply hsub.trans
  simpa only [hnorm] using hminor P hP

#print axioms compactTraceWeylSum_shrinking_pruning
end WaringSiegel.WSL4
