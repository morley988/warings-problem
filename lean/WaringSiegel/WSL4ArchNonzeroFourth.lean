import WaringSiegel.WSL4ArchFourthKappa
import WaringSiegel.WSL3PoissonMixedKMajor

/-! # The literal excluded-zero near-zero source major fourth moment

This is the major fourth integral consumed by the mixed-sixth argument,
with its exact enlarged major set and zero term removed. The only remaining
hypothesis is the literal finite twisted complete-sum domination.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem traceMajorArcUnion_antitone_scale {H J L : ℝ} (hHJ : H ≤ J) :
    traceMajorArcUnion (K:=K) J L ⊆ traceMajorArcUnion H L := by
  intro q hq
  obtain ⟨γ,x,hx,hxq⟩ := Set.mem_iUnion.mp hq
  apply Set.mem_iUnion.mpr
  refine ⟨γ,x,?_,hxq⟩
  exact (mul_le_mul_of_nonneg_left (productArcWeight_mono_scale H J hHJ
    (x-mixedEmbedding K γ)) (Nat.cast_nonneg _)).trans hx

theorem nonzeroCubicMajorArcs_subset (H : ℝ) (hH : 0 ≤ H) :
    nonzeroCubicMajorArcs (K:=K) H ⊆
      traceMajorArcUnion (H^3) ((6:ℝ)^finrank ℚ K*H^finrank ℚ K) := by
  apply traceMajorArcUnion_antitone_scale
  nlinarith [pow_nonneg hH 3]

theorem nearZero_nonzeroCubicMajorFourth_bound
    (ε : ℝ) (hε : 0 < ε)
    (B : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hB : ∀ v, 0 ≤ B v)
    (hfinite : ∀ (γ : K) (ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹)),
      ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
        ((traceConductor γ).absNorm:ℝ)*cubicKappa B ⟨traceConductor γ,traceConductor_ne_zero γ⟩) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ) (hH : 1 ≤ H),
      nonzeroCubicMajorFourth (nearZeroSchwartz (K:=K)) nearZeroSchwartz_majorant.2.1 H (by linarith) ≤
        C*(H^finrank ℚ K : ℝ)^(1+ε) := by
  obtain ⟨C,hC,hb⟩ := nearZeroTraceCubicSum_major_fourth (K:=K)
    ((6:ℝ)^finrank ℚ K) (one_le_pow₀ (by norm_num)) ε hε B hB hfinite
  refine ⟨8*(C+1),by positivity,fun H hH => ?_⟩
  have hH0 : 0 < H := by linarith
  let S := nonzeroCubicMajorArcs (K:=K) H
  let T := traceMajorArcUnion (K:=K) (H^3) ((6:ℝ)^finrank ℚ K*H^finrank ℚ K)
  let f : ArchimedeanTraceTorus K → ℝ := fun q => ‖nearZeroTraceCubicSum H hH0.ne' q‖^4
  let e : ArchimedeanTraceTorus K → ℝ := fun q =>
    ‖compactTraceNonzeroCubicSum nearZeroSchwartz nearZeroSchwartz_majorant.2.1 H hH0.ne' q‖^4
  have hfi : Integrable f traceHaar := (nearZeroTraceCubicSum_continuous H hH0.ne').norm.pow 4
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hei : Integrable e traceHaar := (compactTraceNonzeroCubicSum_continuous _ _ _ _).norm.pow 4
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hS : MeasurableSet S := traceMajorArcUnion_measurableSet _ _ (by positivity)
  have hsub : S ⊆ T := nonzeroCubicMajorArcs_subset H hH0.le
  have hf0 : ∀ q, 0 ≤ f q := fun _ => pow_nonneg (norm_nonneg _) _
  have h01 : nearZeroSchwartz (K:=K) 0 = 1 := nearZeroSchwartz_majorant.2.2.1 0 (by simp)
  have he : ∀ q, e q ≤ 8*(f q+1) := by
    intro q
    simpa only [e,f,nearZeroTraceCubicSum,h01,norm_one,one_pow] using
      compactTraceNonzeroCubicSum_fourth_le nearZeroSchwartz nearZeroSchwartz_majorant.2.1 H hH0.ne' q
  have hconst : (∫ q in S, (1:ℝ) ∂traceHaar) ≤ 1 := by
    have h := setIntegral_le_integral (integrable_const (μ:=traceHaar (K:=K)) (1:ℝ))
      (Filter.Eventually.of_forall (fun _ : ArchimedeanTraceTorus K => zero_le_one)) (s:=S)
    simpa only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] using h
  have hW : 1 ≤ (H^finrank ℚ K : ℝ)^(1+ε) :=
    Real.one_le_rpow (one_le_pow₀ hH) (by linarith)
  calc
    _ = ∫ q in S, e q ∂traceHaar := rfl
    _ ≤ ∫ q in S, 8*(f q+1) ∂traceHaar :=
      setIntegral_mono_on hei.integrableOn ((hfi.add (integrable_const 1)).const_mul 8).integrableOn hS
        (fun q _ => he q)
    _ = 8*((∫ q in S, f q ∂traceHaar)+(∫ q in S, (1:ℝ) ∂traceHaar)) := by
      rw [integral_const_mul,integral_add hfi.integrableOn (integrable_const 1)]
    _ ≤ 8*((∫ q in T, f q ∂traceHaar)+1) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (setIntegral_mono_set hfi.integrableOn (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hsub)) hconst) (by norm_num)
    _ ≤ 8*(C*(H^finrank ℚ K : ℝ)^(1+ε)+1) :=
      mul_le_mul_of_nonneg_left (add_le_add_right (hb H hH) 1) (by norm_num)
    _ ≤ (8*(C+1))*(H^finrank ℚ K : ℝ)^(1+ε) := by nlinarith

#print axioms nearZero_nonzeroCubicMajorFourth_bound
end WaringSiegel.WSL4
