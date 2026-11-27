import WaringDualEnvelope.InfiniteOrders
import WaringLinear.ScheduledTraceMoments

/-! # The linear moment order on the archimedean trace torus -/
noncomputable section
open MeasureTheory
open WaringSiegel WaringSiegel.WSL2 WaringDualEnvelope
namespace WaringLinear.TraceSumFamily
variable {K : Type*} [Field K] [NumberField K] (W : TraceSumFamily K)

/-- An even pair of orders works at every scale in the given number field.
The ordinary major-arc moment controls the restricted moment at the same
order after the outer saving absorbs the old defect. -/
def LossFreeOrders (k : ℕ) (price : ℝ) : Prop :=
    ∃ r a : ℕ, Even r ∧ Even a ∧ ((r+a:ℕ):ℝ)/k<price ∧
      ∀ (M : ℕ → Set (ArchimedeanTraceTorus K)) (A B C : ℝ),
      (∀ X, MeasurableSet (M X)) → 0≤B → 0≤C →
      (∀ X : ℕ, 1≤X → ∀ q∈(M X)ᶜ, ‖W.restricted k X q‖≤C*X) →
      (∀ X : ℕ, 1≤X → ∀ q∈(M X)ᶜ, ‖W.ordinary k X q‖≤B*(X:ℝ)^(1-minorSaving k)) →
      (∀ X : ℕ, 1≤X → (∫ q in M X, ‖W.ordinary k X q‖^(r+a) ∂traceHaar)≤A*(X:ℝ)^((r:ℝ)+a-k)) →
      ∃ E : ℝ, ∀ X : ℕ, 1≤X →
        (∫ q, ‖W.restricted k X q‖^(r+a) ∂traceHaar)≤E*(X:ℝ)^((r:ℝ)+a-k)

theorem linear_loss_free_orders (k : ℕ) (hk : 21≤k)
    (seed : SeedMoments (W.admissible k) k) (step : RealStageUpdate (W.admissible k) k) :
    W.LossFreeOrders k (6874/1000) :=
  W.loss_free_of_order k _ (all_moment_orders_6874 k hk _ seed step)

#print axioms linear_loss_free_orders
end WaringLinear.TraceSumFamily
