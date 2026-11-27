import WaringSiegel.WSL3UnitSourceDensity

/-!
# Absolute convergence and inversion for dominated source measures

Every finite source measure dominated by a positive root box inherits the
actual L² density estimate. Hence its literal root integral has integrable
squared modulus, every power of order at least two is integrable, and its
singular integral equals the genuine continuous source density.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical RealInnerProductSpace
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

variable (k s : ℕ) (hk : 0 < k) {μ : Measure (mixedSpace K)} [IsFiniteMeasure μ]
  (ρ R : ℝ) (hρ : 0 < ρ) (hμ : μ ≤ volume.restrict (rootBox K ρ R))

include hk hρ hμ in
theorem sourceWaringDensity_euclidean_fourier (β : mixedSpace K) :
    Real.fourierIntegral (fun x : euclidean.mixedSpace K =>
      ((sourceWaringDensity k s μ (euclidean.toMixed K x)).toReal : ℂ))
      (-traceFrequency β) = sourceRootIntegral k μ β ^ (s+1) := by
  rw [traceFrequency_fourier (fun x : mixedSpace K =>
    ((sourceWaringDensity k s μ x).toReal : ℂ)) β]
  simpa only [Complex.real_smul, mul_comm] using sourceWaringDensity_fourier k s hk ρ R hρ hμ β

include hk hρ hμ in
theorem sourceContinuousDensity_euclidean_fourier (β : mixedSpace K) :
    Real.fourierIntegral (fun x : euclidean.mixedSpace K =>
      (sourceContinuousDensity k s μ (euclidean.toMixed K x) : ℂ))
      (-traceFrequency β) = sourceRootIntegral k μ β ^ (s+2) := by
  rw [traceFrequency_fourier (fun x : mixedSpace K => (sourceContinuousDensity k s μ x : ℂ)) β]
  simpa only [Complex.real_smul, mul_comm] using sourceContinuousDensity_fourier k s hk ρ R hρ hμ β

include hk hρ hμ in
/-- Genuine frequency L² integrability; no Plancherel premise is assumed. -/
theorem sourceRootIntegral_norm_sq_integrable :
    Integrable (fun β : mixedSpace K => ‖sourceRootIntegral k μ β‖^2) := by
  let f : euclidean.mixedSpace K → ℝ := fun x =>
    (sourceWaringDensity k 0 μ (euclidean.toMixed K x)).toReal
  have hf : Integrable f :=
    (euclidean.volumePreserving_toMixed K).integrable_comp_of_integrable
      (sourceWaringDensity_integrable k 0 μ)
  have h2 : MemLp f 2 := (sourceWaringDensity_memLp_two k 0 hk ρ R hρ hμ).comp_measurePreserving
    (euclidean.volumePreserving_toMixed K)
  have he0 : Integrable (fun ξ : euclidean.mixedSpace K =>
      ‖Real.fourierIntegral (fun x : euclidean.mixedSpace K => (f x : ℂ)) ξ‖^2) :=
    fourier_norm_sq_integrable_real hf h2
  have he : Integrable (fun ξ : euclidean.mixedSpace K =>
      ‖Real.fourierIntegral (fun x : euclidean.mixedSpace K => (f x : ℂ)) (-ξ)‖^2) :=
    (LinearIsometryEquiv.neg ℝ (E := euclidean.mixedSpace K)).measurePreserving.integrable_comp_of_integrable he0
  have ht := (traceFrequency_integrable_comp
    (fun ξ : euclidean.mixedSpace K =>
      ‖Real.fourierIntegral (fun x : euclidean.mixedSpace K => (f x : ℂ)) (-ξ)‖^2)).mpr he
  convert ht using 1
  funext β
  dsimp only [f]
  rw [sourceWaringDensity_euclidean_fourier k 0 hk ρ R hρ hμ]
  simp

include hk hρ hμ in
theorem sourceRootIntegral_pow_integrable :
    Integrable (fun β : mixedSpace K => sourceRootIntegral k μ β ^ (s+2)) := by
  apply ((sourceRootIntegral_norm_sq_integrable k hk ρ R hρ hμ).const_mul
    ((μ Set.univ).toReal^s)).mono' ((sourceRootIntegral_continuous k μ).pow (s+2)).aestronglyMeasurable
  filter_upwards with β
  rw [norm_pow, pow_add]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) (sourceRootIntegral_norm_le k μ β) s

include hk hρ hμ in
theorem sourceRootIntegral_phase_integrable (b : mixedSpace K) :
    Integrable (fun β : mixedSpace K =>
      archimedeanTraceCharacter (-β) b * sourceRootIntegral k μ β ^ (s+2)) := by
  apply (sourceRootIntegral_pow_integrable k s hk ρ R hρ hμ).bdd_mul
  · have hc : Continuous (fun β : mixedSpace K => archimedeanTraceCharacter (-β) b) := by
      simpa only [archimedeanTraceCharacter_symm] using
        (archimedeanTraceCharacter_continuous b).comp continuous_neg
    exact hc.aestronglyMeasurable
  · exact ⟨1, fun β => (archimedeanTraceCharacter_norm (-β) b).le⟩

include hk hρ hμ in
theorem sourceContinuousDensity_fourier_integrable :
    Integrable (Real.fourierIntegral (fun x : euclidean.mixedSpace K =>
      (sourceContinuousDensity k s μ (euclidean.toMixed K x) : ℂ))) := by
  let F : euclidean.mixedSpace K → ℂ := fun x =>
    (sourceContinuousDensity k s μ (euclidean.toMixed K x) : ℂ)
  have hcomp : Integrable (fun β : mixedSpace K => Real.fourierIntegral F (-traceFrequency β)) := by
    have heq : (fun β : mixedSpace K => Real.fourierIntegral F (-traceFrequency β)) =
        (fun β => sourceRootIntegral k μ β ^ (s+2)) :=
      funext (sourceContinuousDensity_euclidean_fourier k s hk ρ R hρ hμ)
    rw [heq]
    exact sourceRootIntegral_pow_integrable k s hk ρ R hρ hμ
  have hn : Integrable (fun ξ : euclidean.mixedSpace K => Real.fourierIntegral F (-ξ)) :=
    (traceFrequency_integrable_comp (fun ξ => Real.fourierIntegral F (-ξ))).mp hcomp
  have hh : Integrable (fun ξ : euclidean.mixedSpace K => Real.fourierIntegral F (-(-ξ))) :=
    (LinearIsometryEquiv.neg ℝ (E := euclidean.mixedSpace K)).measurePreserving.integrable_comp_of_integrable hn
  simpa only [neg_neg] using hh

/-- The source singular integral uses the actual number n of roots. -/
def sourceSingularIntegral (k n : ℕ) (μ : Measure (mixedSpace K)) (b : mixedSpace K) : ℂ :=
  ∫ β : mixedSpace K, archimedeanTraceCharacter (-β) b * sourceRootIntegral k μ β ^ n

include hk hρ hμ in
/-- Exact normalized inversion for the genuine dominated source profile. -/
theorem sourceSingularIntegral_eq_density (b : mixedSpace K) :
    sourceSingularIntegral k (s+2) μ b =
      ((4 : ℝ)^nrComplexPlaces K)⁻¹ • (sourceContinuousDensity k s μ b : ℂ) := by
  have h := trace_fourier_inversion (sourceContinuousDensity_integrable k s μ).ofReal
    (Complex.continuous_ofReal.comp (sourceContinuousDensity_continuous k s hk ρ R hρ hμ))
    (sourceContinuousDensity_fourier_integrable k s hk ρ R hρ hμ) b
  calc
    _ = ∫ β : mixedSpace K, archimedeanTraceCharacter (-β) b *
        Real.fourierIntegral (fun x : euclidean.mixedSpace K =>
          (sourceContinuousDensity k s μ (euclidean.toMixed K x) : ℂ)) (-traceFrequency β) := by
      apply integral_congr_ae
      filter_upwards with β
      rw [sourceContinuousDensity_euclidean_fourier k s hk ρ R hρ hμ β]
    _ = _ := h

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.sourceRootIntegral_pow_integrable
#print axioms WaringSiegel.WSL3.sourceSingularIntegral_eq_density
