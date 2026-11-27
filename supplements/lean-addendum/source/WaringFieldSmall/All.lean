import WaringFieldSmall.Coverage
import WaringFieldSmall.LowConductors
import WaringLinear.OneOrdinaryFieldArcs

/-! # Field orders for all integers k≥11
Below 2501, the finite individual conductors are exposed through
RowCoverage. Above this range the dual-envelope grids prove all
continuum conductivity conditions internally. -/
noncomputable section
open WaringLinear WaringEnvelope
namespace WaringFieldSmall
variable {K : Type*} [Field K] [NumberField K]

theorem field_marked_orders_eleven (W : ℝ → TraceSumFamily K) (k : ℕ) (hk : 11≤k)
    (count : DifferencingCounts W k) (rows : 21≤k → k≤2500 → RowCoverage Listed k)
    (step : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ 0<a ∧ cutoffAdmissible W k r x ∧ 0≤x ∧
      (k:ℝ)*x<((a:ℝ)-1)*(1/(15*k)) ∧ ((r+a+1:ℕ):ℝ)/k<6873/1000 := by
  by_cases small : k≤20
  · obtain ⟨r,a,x,er,ea,ha,mom,hx,gap,_,cost⟩ := degree_eleven_through_twenty W k hk small count step
    exact ⟨r,a,x,er,ea,ha,mom,hx,gap,cost⟩
  by_cases h : k≤2500
  · obtain ⟨r,a,x,er,ea,ha,mom,hx,gap,_,cost⟩ :=
      small_field_marked_orders Listed W k hk (covered k hk h) count
      (roundedShortening_of_physical Listed W k (by omega) (rows (by omega) h) step)
    exact ⟨r,a,x,er,ea,ha,mom,hx,gap,cost⟩
  · exact field_marked_orders_of_differencing W k (by omega) count step

theorem field_loss_free_eleven (W : ℝ → TraceSumFamily K) (k : ℕ) (hk : 11≤k)
    (count : DifferencingCounts W k) (rows : 21≤k → k≤2500 → RowCoverage Listed k)
    (step : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k) :
    ∃ r a : ℕ, Even r ∧ Even a ∧ ((r+a+1:ℕ):ℝ)/k<6873/1000 ∧
      ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ → uniformMarkedMomentAt (W η) k r a (1/(15*k)) := by
  obtain ⟨r,a,x,er,ea,ha,had,_,gap,price⟩ := field_marked_orders_eleven W k hk count rows step
  exact ⟨r,a,er,ea,price,cutoff_marked_loss_free_at W k r a x _ er ea ha had gap⟩

/-- The remaining arc inputs refer to the actual ordinary and marked field
sums. This specialization keeps the integer budget and gives the stated
bounded, totally positive Waring--Siegel property. -/
theorem field_waring_eleven_of_differencing_and_arcs (W : ℝ → TraceSumFamily K) (k : ℕ)
    (hk : 11≤k) (count : DifferencingCounts W k)
    (rows : 21≤k → k≤2500 → RowCoverage Listed k)
    (step : ShorteningStep fieldConductorStage (cutoffAdmissible W k) k)
    (arcs : ∀ r a : ℕ, Even r → Even a → 0<a → ((r+a+1:ℕ):ℝ)/k<6873/1000 →
      ∃ η₀ : ℝ, 0<η₀ ∧ ∀ η : ℝ, 0<η → η≤η₀ →
        Nonempty (MarkedBroadArcBounds (W η) k r a (1/(15*k))) ∧
        UniformOneOrdinaryCore (W η) k r (a-1) (1/(15*k))) :
    ∃ s : ℕ, ((s+1:ℕ):ℝ)/k<6873/1000 ∧ WaringSiegel.WaringSiegelBound K k s := by
  obtain ⟨r,a,x,er,ea,ha,had,_,gap,price⟩ := field_marked_orders_eleven W k hk count rows step
  exact ⟨r+a,price,waring_siegel_of_marked_orders W k r a x _ (by omega) ha er ea had gap
    (arcs r a er ea ha price)⟩

#print axioms field_waring_eleven_of_differencing_and_arcs
#print axioms field_marked_orders_eleven
#print axioms field_loss_free_eleven
end WaringFieldSmall
