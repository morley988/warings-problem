import WaringSiegel.WSL4ArchMixedMajorBound
import WaringSiegel.WSL4ArchMixedComplementBound

/-! # The actual full near-zero mixed-sixth integral

The source is the original finite compact weighted trace integrand. Both
major and complementary contributions are proved, with precisely the
literal finite twisted complete-sum arithmetic interface retained.
-/
noncomputable section
set_option maxHeartbeats 1300000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def nearZeroMixedSIntegral (H P M R : ℝ)
    (hH : H≠0) (hP : P≠0) (hM : M≠0) (hR : R≠0) : ℂ :=
  ∫q,nearZeroMixedSIntegrand (K:=K) H P M R hH hP hM hR q ∂traceHaar

theorem nearZeroMixedSIntegral_bound
    (ε : ℝ) (hε : 0<ε)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v,0<B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0<C ∧ ∀ (P M : ℝ) (hM : 1≤M) (hMP : M^7≤P),
      ‖nearZeroMixedSIntegral (K:=K) (P/M^3) P M (P/M)
          (by have h := (mixed_scale_range hM hMP).2.1; linarith)
          (by have h := (mixed_scale_range hM hMP).1; linarith) (by linarith)
          (by have h := (mixed_scale_range hM hMP).2.2.1; linarith)‖ ≤
        C*(P^finrank ℚ K : ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K : ℝ)^(-(9/2):ℝ) := by
  obtain ⟨CA,hCA,ha⟩ := nearZeroMixedSIntegrand_major_integral_bound ε hε B hB hfinite
  obtain ⟨CC,hCC,hc⟩ := nearZero_compactMixedSComplementIntegral_bound (K:=K)
    nearZeroSchwartz_majorant.1 nearZeroSchwartz_majorant.2.1 nearZeroSchwartz_majorant.2.2.2.2.2
    nearZeroSchwartz_majorant.1.continuous nearZeroSchwartz_majorant.2.1 nearZeroSchwartz_majorant.2.2.2.2.2
    nearZeroSchwartz_majorant.1 nearZeroSchwartz_majorant.2.1 nearZeroSchwartz_majorant.2.2.2.2.2
    hε B (fun v => (hB v).le) hfinite
  refine ⟨CC+CA,add_pos hCC hCA,fun P M hM hMP => ?_⟩
  obtain ⟨hP,hH,hR,hHP,hPH⟩ := mixed_scale_range hM hMP
  have hP0 : 0<P := by linarith
  have hM0 : 0<M := by linarith
  have hH0 : 0<P/M^3 := by linarith
  have hR0 : 0<P/M := by linarith
  let f := nearZeroMixedSIntegrand (K:=K) (P/M^3) P M (P/M) hH0.ne' hP0.ne' hM0.ne' hR0.ne'
  let S := mixedComplementArcs (K:=K) P (P/M^3)
  have hfi : Integrable f traceHaar := (nearZeroMixedSIntegrand_continuous _ _ _ _ _ _ _ _)
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsplit : (∫q in S,f q ∂traceHaar)+(∫q in Sᶜ,f q ∂traceHaar)=∫q,f q ∂traceHaar :=
    integral_add_compl (mixedComplementArcs_measurable P (P/M^3) hP0 hH0) hfi
  change ‖∫q,f q ∂traceHaar‖≤_
  rw [← hsplit]
  calc
    _ ≤ ‖∫q in S,f q ∂traceHaar‖+‖∫q in Sᶜ,f q ∂traceHaar‖ := norm_add_le _ _
    _ ≤ ‖∫q in S,f q ∂traceHaar‖+∫q in Sᶜ,‖f q‖ ∂traceHaar :=
      add_le_add_left (norm_integral_le_integral_norm _) _
    _ ≤ CC*(P^finrank ℚ K : ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K : ℝ)^(-(9/2):ℝ)+
        CA*(P^finrank ℚ K : ℝ)^((7:ℝ)/2+ε)*(M^finrank ℚ K : ℝ)^(-(9/2):ℝ) :=
      add_le_add (hc P M hM hMP) (ha P M hM hMP)
    _ = _ := by ring

#print axioms nearZeroMixedSIntegral_bound
end WaringSiegel.WSL4
