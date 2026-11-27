import WaringSiegel.WSL3MomentGeneralizedHua
import WaringSiegel.WSL2TraceMoments

/-! # The full generalized Hua family on the literal number-field trace torus -/

noncomputable section
open MeasureTheory
open scoped BigOperators NumberField Classical

namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

theorem traceTorus_generalized_hua_moment_bound (k r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α]
      (nodes : α → 𝓞 K), Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ (w : α → ℂ) (W : ℝ), 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ q, ‖traceWeylSum k nodes w q‖^(r*(r+1)) ∂traceHaar) ≤
        C*(P^Module.finrank ℚ K : ℝ)^((r^2 : ℕ)+ε)*W^(r*(r+1)) := by
  obtain ⟨C,hC,hbound⟩ := numberField_generalized_hua_moment_bound (K := K) k r hr hrk hε
  refine ⟨C,hC,?_⟩
  intro P hP α inst nodes hinj hbox w W hW hw
  rw [traceWeylSum_integral_norm_pow]
  exact hbound P hP nodes hinj hbox w W hW hw

#print axioms traceTorus_generalized_hua_moment_bound

end WaringSiegel.WSL3
