import WaringSiegel.WSL3IdealPoissonTrace
import WaringSiegel.WSL3PoissonScaledSmooth

/-!
# Exact trace Poisson formula for every actual ideal coset

The source may be any Schwartz function. The coset shift produces its actual
trace Fourier phase, and the normalization retains Norm(I) and covol(O_K).
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem translation_hasTemperateGrowth (a : mixedSpace K) :
    Function.HasTemperateGrowth (fun x : mixedSpace K => a+x) := by
  have he : fderiv ℝ (fun x : mixedSpace K => a+x) =
      fun _ => ContinuousLinearMap.id ℝ (mixedSpace K) := by
    funext x
    exact ((hasFDerivAt_id x).const_add a).fderiv
  have hd : Function.HasTemperateGrowth (fderiv ℝ (fun x : mixedSpace K => a+x)) := by
    rw [he]
    exact Function.HasTemperateGrowth.const _
  apply Function.HasTemperateGrowth.of_fderiv hd
    (differentiable_const a |>.add differentiable_id) (k := 1) (C := 1+‖a‖)
  intro x
  have h := norm_add_le a x
  simp only [pow_one]
  nlinarith [norm_nonneg a,norm_nonneg x]

def translateSchwartz (a : mixedSpace K) (f : 𝓢(mixedSpace K,ℂ)) : 𝓢(mixedSpace K,ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (translation_hasTemperateGrowth a)
    (isometry_add_left a).antilipschitz f

@[simp] theorem translateSchwartz_apply (a : mixedSpace K) (f : 𝓢(mixedSpace K,ℂ))
    (x : mixedSpace K) : translateSchwartz a f x = f (a+x) := rfl

theorem traceCharacter_frequency_neg_mul (ξ a : mixedSpace K) :
    archimedeanTraceCharacter ξ a * archimedeanTraceCharacter (-ξ) a = 1 := by
  rw [← traceCharacter_frequency_add,add_neg_cancel]
  simp [archimedeanTraceCharacter]

/-- Translation of the actual trace Fourier transform, with positive shift phase. -/
theorem traceFourier_translate (a : mixedSpace K) (f : mixedSpace K → ℂ) (ξ : mixedSpace K) :
    traceFourier (fun x => f (a+x)) ξ = archimedeanTraceCharacter ξ a * traceFourier f ξ := by
  unfold traceFourier
  calc
    _ = ∫ x : mixedSpace K, archimedeanTraceCharacter ξ a *
        (archimedeanTraceCharacter (-ξ) (a+x)*f (a+x)) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [archimedeanTraceCharacter_add,← mul_assoc,← mul_assoc,
        traceCharacter_frequency_neg_mul,one_mul]
    _ = archimedeanTraceCharacter ξ a *
        (∫ x : mixedSpace K, archimedeanTraceCharacter (-ξ) (a+x)*f (a+x)) := integral_const_mul _ _
    _ = _ := congrArg (fun z : ℂ => archimedeanTraceCharacter ξ a*z)
      (integral_add_left_eq_self (fun x : mixedSpace K => archimedeanTraceCharacter (-ξ) x*f x) a)

/-- Actual affine ideal-coset Poisson, with dual D^-1 I^-1 and the literal
positive phase attached to the shift. -/
theorem poisson_fractionalIdeal_coset (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : mixedSpace K) (f : 𝓢(mixedSpace K,ℂ)) :
    (∑' x : (I : FractionalIdeal (𝓞 K)⁰ K), f (a+mixedEmbedding K (x:K))) =
      ((FractionalIdeal.absNorm I.1:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
        (∑' ξ : fractionalTraceDual I,
          archimedeanTraceCharacter (mixedEmbedding K (ξ:K)) a *
            traceFourier f (mixedEmbedding K (ξ:K))) := by
  have h := poisson_fractionalIdeal_schwartz I (translateSchwartz a f)
  simpa only [translateSchwartz_apply,show (translateSchwartz a f : mixedSpace K → ℂ) =
    (fun x => f (a+x)) from rfl,traceFourier_translate] using h

/-- The same exact formula with the geometric field covolume expanded. -/
theorem poisson_fractionalIdeal_coset_discriminant (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : mixedSpace K) (f : 𝓢(mixedSpace K,ℂ)) :
    (∑' x : (I : FractionalIdeal (𝓞 K)⁰ K), f (a+mixedEmbedding K (x:K))) =
      ((FractionalIdeal.absNorm I.1:ℝ)*(2⁻¹:ℝ)^NumberField.InfinitePlace.nrComplexPlaces K *
          Real.sqrt |(NumberField.discr K:ℝ)|)⁻¹ •
        (∑' ξ : fractionalTraceDual I,
          archimedeanTraceCharacter (mixedEmbedding K (ξ:K)) a *
            traceFourier f (mixedEmbedding K (ξ:K))) := by
  rw [poisson_fractionalIdeal_coset,integer_basisCovolume]
  congr 2
  ring

#print axioms traceFourier_translate
#print axioms poisson_fractionalIdeal_coset
#print axioms poisson_fractionalIdeal_coset_discriminant
end WaringSiegel.WSL3Poisson
