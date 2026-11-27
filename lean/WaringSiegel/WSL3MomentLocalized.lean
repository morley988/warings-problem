import WaringSiegel.WSL3MomentLocalizedMajorant

/-! # The actual localized number-field moment

For k=R+2≥3, the exponent outside the full Vinogradov count is
R(R+1)/2+R = k(k-1)/2-1. Both the trace Haar integral and the enlarged node
set are literal, and the top equation is imposed by proved orthogonality.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module GafniTao
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

/-- Localized moment with its full extra volume power and actual full-system
solution count. Constants and the enlarged support precede the frequency. -/
theorem compactTraceWeylSum_localized_moment_bound
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (R s : ℕ) (hR : 1 ≤ R) (hs : 1 ≤ s) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧ ∀ (P : ℝ) (hP : 1 ≤ P),
      ∃ T : Finset (𝓞 K),
        (∀ x∈T, ∀ v : InfinitePlace K, v (x:K) ≤ A*P) ∧
        (∫ q in vinogradovMinorArcs (K := K) (R+2) P,
          ‖compactTraceWeylSum (R+2) f hc P (by linarith) q‖^(2*s) ∂traceHaar) ≤
            C * (P^finrank ℚ K)^(wooleyTriangular R+R) *
              (vinogradovCount (R+2) s (fun a : T => a.val) : ℝ) := by
  obtain ⟨C, A, hC, hA, hb⟩ := compactTraceWeylSum_minor_majorant f hc R s hR hs
  refine ⟨C, A, hC, hA, ?_⟩
  intro P hP
  obtain ⟨T, hT, hbound⟩ := hb P hP
  refine ⟨T, hT, ?_⟩
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let F : ArchimedeanTraceTorus K → ℝ :=
    fun q => ‖compactTraceWeylSum (R+2) f hc P hP0.ne' q‖^(2*s)
  let G : ArchimedeanTraceTorus K → ℝ :=
    fun q => monomialSliceIntegral (integerCoordinates K) R s (fun a : T => a.val)
      (archimedeanTraceTorusContinuousAddEquiv q)
  let D : ℝ := C*(P^finrank ℚ K)^(wooleyTriangular R+R)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hFcont : Continuous F := (compactTraceWeylSum_continuous _ _ _ _ _).norm.pow _
  have hGcont : Continuous G :=
    (monomialSliceIntegral_continuous (integerCoordinates K) (integerCoordinates_injective K)
      R s (fun a : T => a.val)).comp archimedeanTraceTorusContinuousAddEquiv.continuous
  have hiF : Integrable F traceHaar := hFcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hiG : Integrable G traceHaar := hGcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hG0 : ∀ q, 0 ≤ G q := fun q => monomialSliceIntegral_nonneg _ _ _ _ _
  have hfull : (∫ q, G q ∂traceHaar) = (vinogradovCount (R+2) s (fun a : T => a.val) : ℝ) := by
    rw [show G = fun q => monomialSliceIntegral (integerCoordinates K) R s
        (fun a : T => a.val) (archimedeanTraceTorusContinuousAddEquiv q) from rfl,
      traceHaar_integral_coordinates]
    exact integral_monomialSliceIntegral (integerCoordinates K) (integerCoordinates_injective K) R s _
  calc
    _ ≤ ∫ q in vinogradovMinorArcs (K := K) (R+2) P, D*G q ∂traceHaar :=
      setIntegral_mono_on hiF.integrableOn (hiG.const_mul D).integrableOn
        (vinogradovMinorArcs_measurable _ _ hP0) hbound
    _ = D * ∫ q in vinogradovMinorArcs (K := K) (R+2) P, G q ∂traceHaar := integral_const_mul _ _
    _ ≤ D * ∫ q, G q ∂traceHaar := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hiG (Filter.Eventually.of_forall hG0)) hD
    _ = _ := by rw [hfull]

#print axioms compactTraceWeylSum_localized_moment_bound
end WaringSiegel.WSL3
