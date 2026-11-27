import Waring.CertificateAllocation
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Uniform constants across the actual continuous height interval -/
noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionResourceCompact
open Certificate

theorem resourceReal_continuous (k : ℕ) (p : Policy) (coefficient : Curve) (r : Resource) :
    Continuous (resourceReal k p coefficient r) := by
  unfold resourceReal
  cases r.kind <;> fun_prop

theorem resourceReal_uniform_bound {ρ : Type*} [Fintype ρ]
    (k : ℕ) (p : Policy) (coefficient : Curve) (resources : ρ → Resource) (top : ℝ) :
    ∃ B : ℝ,0<B ∧ ∀ r : ρ,∀ ell∈Set.Icc 0 top,
      |resourceReal k p coefficient (resources r) ell|≤B := by
  have hex : ∀ r : ρ,∃ C : ℝ,∀ ell∈Set.Icc 0 top,
      |resourceReal k p coefficient (resources r) ell|≤C := by
    intro r
    simpa only [Real.norm_eq_abs] using isCompact_Icc.exists_bound_of_continuousOn
      (resourceReal_continuous k p coefficient (resources r)).continuousOn
  choose C hC using hex
  refine ⟨1+∑r,|C r|,by positivity,?_⟩
  intro r ell hell
  apply (hC r ell hell).trans
  have hs : |C r|≤∑q,|C q| := Finset.single_le_sum (fun q _ => abs_nonneg (C q)) (Finset.mem_univ r)
  linarith [le_abs_self (C r)]

#print axioms resourceReal_uniform_bound
end Waring.PolicyCompletionResourceCompact
