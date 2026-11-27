import WaringLinear.OneOrdinaryFieldArcs
import WaringLinear.FieldMarkedEndgame

/-! # The number-field linear bound with the marked minor-arc saving -/
noncomputable section
open WaringSiegel WaringSiegel.WSL2 WaringEnvelope WaringDualEnvelope
namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

/-- At degree at least 2501, all arithmetic costs, the seed-order conversion,
the loss-free moment, and the choice of core width and scale are formalized.
The analytic assumptions are on power-equality counts and the ordinary and
marked trace Weyl sums at the chosen degree. -/
theorem field_waring_of_differencing_and_arcs (W : ℝ → TraceSumFamily K) (k : ℕ)
    (hk : 2501≤k) (count : DifferencingCounts W k)
    (shorten : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k)
    (arcs : ∀ r a : ℕ, Even r → Even a → 0<a → ((r+a+1:ℕ):ℝ)/k<6873/1000 →
      ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
        Nonempty (MarkedBroadArcBounds (W η) k r a (1/(15*k))) ∧
        UniformOneOrdinaryCore (W η) k r (a-1) (1/(15*k))) :
    ∃ s : ℕ, ((s+1:ℕ):ℝ)/k<6873/1000 ∧ WaringSiegelBound K k s := by
  obtain ⟨r,a,x,er,ea,ha,had,_,gap,price⟩ := field_marked_orders_of_differencing W k hk count shorten
  exact ⟨r+a,price,waring_siegel_of_marked_orders W k r a x _ (by omega) ha er ea had gap
    (arcs r a er ea ha price)⟩

#print axioms field_waring_of_differencing_and_arcs
end WaringLinear
