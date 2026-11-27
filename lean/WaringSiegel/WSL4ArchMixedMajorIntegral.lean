import WaringSiegel.WSL4ArchMixedMajorPointwise
import WaringSiegel.WSL4ArchMixedKernelUnion
import WaringSiegel.WSL4ArchNonzeroFourth

/-! # Major-arc integration of the literal mixed-sixth source -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem nearZeroMixedSIntegrand_major_integral_volume_bound
    (L : ℝ) (hL : 1≤L) (ε δ : ℝ) (hε : 0<ε) (hδ : 0<δ)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0<B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0<C ∧ ∀ (H P M R : ℝ) (hH : 1≤H) (hP : 1≤P) (hM : 1≤M) (hR : 1≤R),
      H≤P → P≤H^2 → R^3=P^2*H →
      (∫q in traceMajorArcUnion (K:=K) (P^2*H) (L*P^finrank ℚ K),
        ‖nearZeroMixedSIntegrand (K:=K) H P M R
          (by linarith) (by linarith) (by linarith) (by linarith) q‖ ∂traceHaar) ≤
        C*H^finrank ℚ K*P^finrank ℚ K*P^ε*M^finrank ℚ K*
          ((P^2*H)^finrank ℚ K)⁻¹*((R^finrank ℚ K)^4+(L*P^finrank ℚ K)^((7/2:ℝ)+2*δ)) := by
  obtain ⟨CA,hCA,ha⟩ := nearZeroMixedSIntegrand_major_bound L hL ε hε B hB hfinite
  obtain ⟨CK,hCK,hk⟩ := mixedMajorKernel_union_bound B (fun v => (hB v).le) δ hδ
  refine ⟨CK*CA,mul_pos hCK hCA,fun H P M R hH hP hM hR hHP hPH hscale => ?_⟩
  have hH0 : 0<H := by linarith
  have hP0 : 0<P := by linarith
  have hM0 : 0<M := by linarith
  have hR0 : 0<R := by linarith
  let V := CA*H^finrank ℚ K*P^finrank ℚ K*P^ε*M^finrank ℚ K
  let f : ArchimedeanTraceTorus K → ℝ := fun q =>
    ‖nearZeroMixedSIntegrand H P M R hH0.ne' hP0.ne' hM0.ne' hR0.ne' q‖
  have hh := hk (P^2*H) (L*P^finrank ℚ K) V (R^finrank ℚ K) (by positivity)
    (one_le_mul_of_one_le_of_one_le hL (one_le_pow₀ hP)) (by dsimp [V]; positivity)
    (pow_nonneg hR0.le _) f (nearZeroMixedSIntegrand_continuous _ _ _ _ _ _ _ _).norm
    (fun _ => norm_nonneg _) (by
      intro γ θ hθ
      have hne : traceConductor γ≠0 := traceConductor_ne_zero γ
      simp only [cubicKappaIdeal,dif_neg hne]
      exact ha H P M R hH hP hM hR hHP hPH hscale θ γ hθ)
  exact hh.trans_eq (by dsimp only [V]; ring)

theorem nearZeroMixedSIntegrand_actual_major_integral_le
    (H P M R : ℝ) (hH : 0<H) (hP : 0<P) (hM : M≠0) (hR : R≠0) :
    (∫q in (mixedComplementArcs (K:=K) P H)ᶜ,
      ‖nearZeroMixedSIntegrand H P M R hH.ne' hP.ne' hM hR q‖ ∂traceHaar) ≤
    (∫q in traceMajorArcUnion (K:=K) (P^2*H) ((6:ℝ)^finrank ℚ K*P^finrank ℚ K),
      ‖nearZeroMixedSIntegrand H P M R hH.ne' hP.ne' hM hR q‖ ∂traceHaar) := by
  have hc := (nearZeroMixedSIntegrand_continuous (K:=K) H P M R hH.ne' hP.ne' hM hR).norm
  have hi : Integrable (fun q : ArchimedeanTraceTorus K =>
      ‖nearZeroMixedSIntegrand H P M R hH.ne' hP.ne' hM hR q‖) traceHaar :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply setIntegral_mono_set hi.integrableOn (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
  apply Filter.Eventually.of_forall
  simp only [mixedComplementArcs,compl_compl]
  exact traceMajorArcUnion_antitone_scale (by nlinarith [sq_nonneg P])

#print axioms nearZeroMixedSIntegrand_major_integral_volume_bound
#print axioms nearZeroMixedSIntegrand_actual_major_integral_le
end WaringSiegel.WSL4
