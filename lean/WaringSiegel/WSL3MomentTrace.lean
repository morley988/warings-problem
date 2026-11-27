import WaringSiegel.WSL3MomentHuaWeighted
import WaringSiegel.WSL2TraceMoments

/-!
# All Hua moments on the literal trace quotient

The domain is V / D⁻¹ with its proved probability Haar measure and the
trace exponential.  The coordinate change is the established continuous
additive equivalence, and carries no unproved measure-normalization premise.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NumberField Classical

namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

/-- The complete classical Hua family on the manuscript's trace torus. -/
theorem traceTorus_hua_moment_bound (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K, Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℂ, ∀ W : ℝ, 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ q, ‖traceWeylSum k nodes w q‖^(2^j) ∂traceHaar) ≤
        C * (P ^ Module.finrank ℚ K : ℝ)^((2^j-j : ℕ)+ε) * W^(2^j) := by
  obtain ⟨C, hC, hbound⟩ := numberField_hua_moment_bound (K := K) k j hj hjk hε
  refine ⟨C, hC, ?_⟩
  intro P hP α inst nodes hinj hbox w W hW hw
  rw [traceWeylSum_integral_norm_pow]
  exact hbound P hP nodes hinj hbox w W hW hw

#print axioms traceTorus_hua_moment_bound

end WaringSiegel.WSL3
