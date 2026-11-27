import WaringSharp.Orders
import WaringSharpTail.Orders

/-! # Even moment orders for every degree at least twenty-one -/
noncomputable section
namespace WaringSharp
open WaringEnvelope WaringDualEnvelope

/-- One extra ordinary variable still fits the allowance at every degree.
The finite range uses the conservative exponent-pair rule, and the remaining
degrees use the residue-stable Fourier rule for the arithmetic B-process. -/
theorem all_orders_with_extra_6873 (k : ℕ) (hk : 21≤k) (P : ℕ → ℝ → Prop)
    (seed : SeedMoments P k)
    (finiteStep : k<180000^2 → StageUpdate DualStage P k)
    (tailStep : 180000^2≤k → WaringSharpTail.Update P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a+1:ℕ):ℝ)/k<6873/1000 := by
  by_cases h : k<180000^2
  · exact finite_orders_with_extra_6873 k hk h P seed (finiteStep h)
  · have hi := le_of_not_gt h
    obtain ⟨r,a,x,er,ea,hP,hx,hgap,hp⟩ := WaringSharpTail.large_degree_order hi P
      (seed WaringSharpTail.z₀ (by decide) (by decide)) (tailStep hi)
    exact ⟨r,a,x,er,ea,hP,hx,hgap,hp.trans (by norm_num)⟩

theorem small_degree_prices : ∀ k : Fin 21, 1≤k.val →
    1000*WaringEnvelope.smallBounds[k.val]!≤6873*k.val := by decide +kernel

#print axioms small_degree_prices
#print axioms all_orders_with_extra_6873
end WaringSharp
