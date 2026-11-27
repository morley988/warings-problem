import WaringLinear.CutoffTraceMoments
import WaringSharp.ShorteningOrders

/-! # The sharpened high moment for actual trace sums -/
noncomputable section
open WaringDualEnvelope WaringEnvelope
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

theorem cutoff_sharp_loss_free (W : ℝ → TraceSumFamily K) (k : ℕ) (hk : 21≤k)
    (seed : SelectedSeeds (cutoffAdmissible W k) k)
    (small : k<180000^2 → ShorteningStep DualStage (cutoffAdmissible W k) k)
    (large : 180000^2≤k → ShorteningStep WaringSharpTail.Branch (cutoffAdmissible W k) k) :
    ∃ r a : ℕ, Even r ∧ Even a ∧ ((r+a+1:ℕ):ℝ)/k<6873/1000 ∧
      ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ → uniformMomentAt (W η) k r a := by
  obtain ⟨r,a,x,er,ea,had,hx,gap,price⟩ :=
    WaringSharp.all_shortening_orders_with_extra_6873 k hk _ seed small large
  exact ⟨r,a,er,ea,price,cutoff_loss_free_at W k r a x er ea had hx gap⟩

#print axioms cutoff_sharp_loss_free
end WaringLinear
