import WaringSiegel.WSL3LocalAbsoluteSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-! # WSL3: absolute finite-subset expansions for the conductor Euler product -/
noncomputable section
open Filter Topology
open scoped BigOperators Classical
namespace WaringSiegel

theorem summable_finset_products_of_nonneg {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hs : Summable f) :
    Summable (fun s : Finset ι => ∏ i ∈ s, f i) := by
  apply summable_of_sum_le (c := Real.exp (∑' i, f i))
    (fun _ => Finset.prod_nonneg (fun i _ => hf i))
  intro U
  let S : Finset ι := U.biUnion id
  have hUS : U ⊆ S.powerset := by
    intro s hs
    rw [Finset.mem_powerset]
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨s, hs, hi⟩
  calc
    _ ≤ ∑ s ∈ S.powerset, ∏ i ∈ s, f i :=
      Finset.sum_le_sum_of_subset_of_nonneg hUS
        (fun s _ _ => Finset.prod_nonneg (fun i _ => hf i))
    _ = ∏ i ∈ S, (1 + f i) := (Finset.prod_one_add S).symm
    _ ≤ ∏ i ∈ S, Real.exp (f i) := by
      apply Finset.prod_le_prod (fun i _ => by linarith [hf i])
      intro i _
      linarith [Real.add_one_le_exp (f i)]
    _ = Real.exp (∑ i ∈ S, f i) := (Real.exp_sum S f).symm
    _ ≤ Real.exp (∑' i, f i) :=
      Real.exp_le_exp.mpr (hs.sum_le_tsum S (fun i _ => hf i))

theorem summable_norm_finset_products {ι : Type*} (f : ι → ℂ)
    (hs : Summable (fun i => ‖f i‖)) :
    Summable (fun s : Finset ι => ‖∏ i ∈ s, f i‖) := by
  simpa only [norm_prod] using
    summable_finset_products_of_nonneg (fun i => ‖f i‖) (fun _ => norm_nonneg _) hs

/-- Every absolutely summable complex family has an absolutely convergent
finite-subset expansion of its Euler product. -/
theorem complex_euler_finset_expansion {ι : Type*} (f : ι → ℂ)
    (hs : Summable (fun i => ‖f i‖)) :
    Multipliable (fun i => 1 + f i) ∧
      (∏' i, (1 + f i)) = ∑' s : Finset ι, ∏ i ∈ s, f i := by
  have h := (summable_norm_finset_products f hs).of_norm
  exact ⟨multipliable_one_add_of_summable_prod h, tprod_one_add h⟩

end WaringSiegel
