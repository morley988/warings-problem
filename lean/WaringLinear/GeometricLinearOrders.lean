import WaringLinear.SmoothSeedSubsets
import WaringSharp.ShorteningOrders

/-! # A linear order from the unconditional geometric smooth seed

This version uses the first-step smooth bound already formalized over the
integers. Only the new shortening step and the passage from arbitrary
smooth subsets to the chosen marked family remain as inputs.
-/
noncomputable section
namespace WaringLinear
open WaringEnvelope WaringDualEnvelope
variable {C : ℕ → ℝ → ℝ → ℝ → Prop} {P : ℕ → ℝ → Prop}

theorem shifted_shortening {k : ℕ} (step : ShorteningStep C P k) :
    ShorteningStep C (fun r x => P (r+seedShift k) x) k := by
  intro r x z M hk er hP hx hz hm hmk hconduct
  have he : Even (seedShift k) := ⟨k+2,by unfold seedShift;omega⟩
  have hh := step (r+seedShift k) x z M (by omega) (er.add he) hP hx hz hm hmk hconduct
  simpa only [show r+2+seedShift k=r+seedShift k+2 by omega] using hh

/-- The full seed is supplied by the verified smooth mean value, for any
family for which subset estimates transfer. -/
theorem geometric_linear_orders (k : ℕ) (hk : 21≤k) (P : ℕ → ℝ → Prop)
    (roots : ∀ r x, SubsetMoment k r x → P r x)
    (finiteStep : k<180000^2 → ShorteningStep DualStage P k)
    (largeStep : 180000^2≤k → ShorteningStep WaringSharpTail.Branch P k) :
    ∃ r a : ℕ, ∃ x : ℝ, Even r ∧ Even a ∧ P r x ∧ 0≤x ∧
      (k:ℝ)*x<(a:ℝ)/((k:ℝ)*(Real.log k+802113/100000)) ∧
      ((r+a+1:ℕ):ℝ)<(8873:ℝ)/1000*k+4 := by
  let Q (r : ℕ) (x : ℝ) := P (r+seedShift k) x
  have seed : SelectedSeeds Q k :=
    fun z hlo hhi => roots _ _ (shifted_subset_seed k z (by omega) hlo hhi)
  obtain ⟨r,a,x,er,ea,hP,hx,hgap,hprice⟩ := WaringSharp.all_shortening_orders_with_extra_6873 k hk Q seed
    (fun h => shifted_shortening (finiteStep h)) (fun h => shifted_shortening (largeStep h))
  have he : Even (seedShift k) := ⟨k+2,by unfold seedShift;omega⟩
  refine ⟨r+seedShift k,a,x,er.add he,ea,hP,hx,hgap,?_⟩
  have hk' : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have h := (div_lt_iff₀ hk').mp hprice
  unfold seedShift
  push_cast at h ⊢
  linarith only [h]

#print axioms geometric_linear_orders
end WaringLinear
