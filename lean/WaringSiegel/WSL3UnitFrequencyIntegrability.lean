import WaringSiegel.WSL3UnitFourierEnergy
import WaringSiegel.WSL3UnitTraceFrequency
import WaringSiegel.WSL2UnitPointwiseFourier

/-!
# Absolute frequency integrability of the actual root integrals

The one-root image density has already been proved to lie in L¹∩L². The
Gaussian/autocorrelation argument now gives a genuine integrable squared
Fourier modulus. The literal trace coordinate change transports this to the
actual root integral, and its proved box-volume bound gives every power of
order at least two. There is no frequency-integrability hypothesis.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical RealInnerProductSpace
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

theorem archimedeanWaringDensity_euclidean_fourier (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (β : mixedSpace K) :
    Real.fourierIntegral (fun x : euclidean.mixedSpace K =>
      ((archimedeanWaringDensity k s ρ R (euclidean.toMixed K x)).toReal : ℂ))
      (-traceFrequency β) = archimedeanRootIntegral k ρ R β ^ (s+1) := by
  rw [traceFrequency_fourier (fun x : mixedSpace K =>
    ((archimedeanWaringDensity k s ρ R x).toReal : ℂ)) β]
  have h := archimedeanWaringDensity_fourier k s hk ρ R hρ β
  simpa only [Complex.real_smul, mul_comm] using h

theorem continuousArchimedeanDensity_euclidean_fourier (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (β : mixedSpace K) :
    Real.fourierIntegral (fun x : euclidean.mixedSpace K =>
      (continuousArchimedeanDensity k s ρ R (euclidean.toMixed K x) : ℂ))
      (-traceFrequency β) = archimedeanRootIntegral k ρ R β ^ (s+2) := by
  rw [traceFrequency_fourier (fun x : mixedSpace K =>
    (continuousArchimedeanDensity k s ρ R x : ℂ)) β]
  have h := continuousArchimedeanDensity_fourier k s hk ρ R hρ β
  simpa only [Complex.real_smul, mul_comm] using h

/-- The actual one-root oscillatory integral has integrable squared modulus. -/
theorem archimedeanRootIntegral_norm_sq_integrable (k : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Integrable (fun β : mixedSpace K => ‖archimedeanRootIntegral k ρ R β‖^2) := by
  let f : euclidean.mixedSpace K → ℝ := fun x =>
    (archimedeanWaringDensity k 0 ρ R (euclidean.toMixed K x)).toReal
  have hf : Integrable f :=
    (euclidean.volumePreserving_toMixed K).integrable_comp_of_integrable
      (archimedeanWaringDensity_integrable k 0 ρ R)
  have h2 : MemLp f 2 := (archimedeanWaringDensity_memLp_two k 0 hk ρ R hρ).comp_measurePreserving
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
  rw [archimedeanWaringDensity_euclidean_fourier k 0 hk ρ R hρ]
  simp

/-- Every actual root-integral power of order s+2 is absolutely integrable. -/
theorem archimedeanRootIntegral_pow_integrable (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Integrable (fun β : mixedSpace K => archimedeanRootIntegral k ρ R β ^ (s+2)) := by
  let C := (volume (rootBox K ρ R)).toReal
  apply ((archimedeanRootIntegral_norm_sq_integrable (K := K) k hk ρ R hρ).const_mul
    (C^s)).mono' ((archimedeanRootIntegral_continuous k ρ R).pow (s+2)).aestronglyMeasurable
  filter_upwards with β
  rw [norm_pow, pow_add]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) (archimedeanRootIntegral_norm_le k ρ R β) s

/-- The literal singular-integral integrand is absolutely integrable at
any target, without a target-dependent integrability premise. -/
theorem archimedeanRootIntegral_phase_integrable (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (b : mixedSpace K) :
    Integrable (fun β : mixedSpace K =>
      archimedeanTraceCharacter (-β) b * archimedeanRootIntegral k ρ R β ^ (s+2)) := by
  apply (archimedeanRootIntegral_pow_integrable k s hk ρ R hρ).bdd_mul
  · have hc : Continuous (fun β : mixedSpace K => archimedeanTraceCharacter (-β) b) := by
      simpa only [archimedeanTraceCharacter_symm] using
        (archimedeanTraceCharacter_continuous b).comp continuous_neg
    exact hc.aestronglyMeasurable
  · exact ⟨1, fun β => (archimedeanTraceCharacter_norm (-β) b).le⟩

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.archimedeanRootIntegral_norm_sq_integrable
#print axioms WaringSiegel.WSL3.archimedeanRootIntegral_pow_integrable
