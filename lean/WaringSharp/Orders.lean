import WaringSharp.Finite
import WaringSharp.ExtraAllowance
import WaringDualEnvelope.FiniteOrders

/-! # Sharper finite integer moment orders with an additional variable -/
noncomputable section
namespace WaringSharp
open WaringEnvelope WaringDualEnvelope

theorem finite_orders_with_extra_6873 (k : ℕ) (lo : 21≤k) (hi : k<180000^2)
    (P : ℕ → ℝ → Prop) (seed : SeedMoments P k) (step : StageUpdate DualStage P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a+1:ℕ):ℝ)/k<6873/1000 := by
  obtain ⟨c,hl,hr,hfin,sz,hc⟩ := finite_selected_6873 k lo hi
  obtain ⟨r,a,x,er,ea,hP,hx,hgap,hprice⟩ := finite_certified_order c _ k P lo hl hr hfin sz hc seed step
  refine ⟨r,a,x,er,ea,hP,hx,hgap,?_⟩
  have cfg := hc.1
  simp only [WaringDualEnvelope.configOK,Bool.and_eq_true,decide_eq_true_eq] at cfg
  have hK : 1≤c.first := by omega
  have hb := extra_variable_allowance c.first k hK hl
  rw [Nat.cast_add,Nat.cast_one,add_div]
  exact (add_lt_add_right hprice _).trans_le hb

#print axioms finite_orders_with_extra_6873
end WaringSharp
