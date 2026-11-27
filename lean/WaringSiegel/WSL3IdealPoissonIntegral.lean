import WaringSiegel.WSL3IdealPoissonCoset

/-!
# The trace Poisson formula indexed by an actual integral ideal
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def integralIdealAsUnit (I : Ideal (𝓞 K)) (hI : I ≠ 0) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (FractionalIdeal.coeIdeal_ne_zero.mpr hI)

def integralIdealFractionalMap (I : Ideal (𝓞 K)) (a : I) : (I : FractionalIdeal (𝓞 K)⁰ K) :=
  ⟨(a:𝓞 K),FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ a.2⟩

theorem integralIdealFractionalMap_bijective (I : Ideal (𝓞 K)) :
    Function.Bijective (integralIdealFractionalMap (K:=K) I) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have hv : ((x:𝓞 K):K) = ((y:𝓞 K):K) :=
      congrArg (fun z : (I : FractionalIdeal (𝓞 K)⁰ K) => (z:K)) h
    exact NumberField.RingOfIntegers.coe_injective hv
  · intro x
    obtain ⟨a,ha,he⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp x.2
    refine ⟨⟨a,ha⟩,Subtype.ext ?_⟩
    exact he

def integralIdealFractionalEquiv (I : Ideal (𝓞 K)) : I ≃ (I : FractionalIdeal (𝓞 K)⁰ K) :=
  Equiv.ofBijective (integralIdealFractionalMap I) (integralIdealFractionalMap_bijective I)

/-- Exact Poisson for an actual ideal coset, indexed by elements of that
integral ideal rather than by chosen basis coordinates. -/
theorem poisson_integralIdeal_coset (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (a : mixedSpace K) (f : 𝓢(mixedSpace K,ℂ)) :
    (∑' x : I, f (a+mixedEmbedding K ((x:𝓞 K):K))) =
      ((I.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
        (∑' ξ : (inverseDifferent K * (I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
          archimedeanTraceCharacter (mixedEmbedding K (ξ:K)) a *
            traceFourier f (mixedEmbedding K (ξ:K))) := by
  have h := poisson_fractionalIdeal_coset (integralIdealAsUnit I hI) a f
  calc
    _ = ∑' x : (I : FractionalIdeal (𝓞 K)⁰ K), f (a+mixedEmbedding K (x:K)) := by
      exact (integralIdealFractionalEquiv (K:=K) I).tsum_eq
        (fun x : (I : FractionalIdeal (𝓞 K)⁰ K) => f (a+mixedEmbedding K (x:K)))
    _ = _ := by
      simpa only [integralIdealAsUnit,Units.val_mk0,fractionalTraceDual,
        FractionalIdeal.coeIdeal_absNorm,Rat.cast_natCast] using h

#print axioms poisson_integralIdeal_coset
end WaringSiegel.WSL3Poisson
