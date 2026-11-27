import WaringSiegel.WSL3MomentRepresentationFourier
import WaringSiegel.WSL3PoissonScaledSmooth

/-! # The actual positive smooth cutoff gives the required representation height -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem smoothWeightSchwartz_hasCompactSupport
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) :
    HasCompactSupport (smoothWeightSchwartz (K := K) ρ R hρ hR : mixedSpace K → ℂ) := by
  have he : (smoothWeightSchwartz (K := K) ρ R hρ hR : mixedSpace K → ℂ) =
      fun x => (smoothRootWeight ρ R x : ℂ) :=
    funext (smoothWeightSchwartz_apply ρ R hρ hR)
  rw [he]
  exact (smoothRootWeight_hasCompactSupport ρ R hρ hR).comp_left
    (g := Complex.ofReal) (by simp)

theorem smoothWeightSchwartz_support_subset
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) :
    Function.support (smoothWeightSchwartz (K := K) ρ R hρ hR : mixedSpace K → ℂ) ⊆
      rootBox K (ρ/2) (2*R) := by
  intro x hx
  apply smoothRootWeight_support_subset ρ R hρ hR
  intro hn
  apply hx
  rw [smoothWeightSchwartz_apply,hn,Complex.ofReal_zero]

theorem representable_of_smoothRootFourier_ne_zero
    (k s : ℕ) (hk : 0<k) (target : 𝓞 K) (htarget : target≠0)
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (hne : (∫ q,
      (compactTraceWeylSum k (smoothWeightSchwartz ρ R hρ hR)
        (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR)
        (rootScale k target) (rootScale_pos htarget k).ne' q)^s *
        traceTorusCharacter (-target) q ∂traceHaar) ≠ 0) :
    RepresentableByAtMost k s ((2*R)^finrank ℚ K) target := by
  apply representable_of_compactTraceFourier_ne_zero k s hk target htarget
    (fun _ => smoothWeightSchwartz ρ R hρ hR)
    (fun _ => smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) (ρ/2) (2*R)
    (by positivity) (fun _ => smoothWeightSchwartz_support_subset ρ R hρ hR)
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hne

theorem representable_of_smoothRootFourier_pos
    (k s : ℕ) (hk : 0<k) (target : 𝓞 K) (htarget : target≠0)
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (hpos : 0 < (∫ q,
      (compactTraceWeylSum k (smoothWeightSchwartz ρ R hρ hR)
        (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR)
        (rootScale k target) (rootScale_pos htarget k).ne' q)^s *
        traceTorusCharacter (-target) q ∂traceHaar).re) :
    RepresentableByAtMost k s ((2*R)^finrank ℚ K) target := by
  apply representable_of_smoothRootFourier_ne_zero k s hk target htarget ρ R hρ hR
  intro hz
  rw [hz,Complex.zero_re] at hpos
  exact lt_irrefl _ hpos

#print axioms representable_of_smoothRootFourier_ne_zero
#print axioms representable_of_smoothRootFourier_pos
end WaringSiegel.WSL3
