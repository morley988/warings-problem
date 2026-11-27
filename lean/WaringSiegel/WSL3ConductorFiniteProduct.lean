import WaringSiegel.WSL3ConductorEulerBase
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic

/-! # WSL3: finite products of absolutely convergent complex series -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical
namespace WaringSiegel

theorem complex_fin_product_hasSum (d : ℕ)
    (f : Fin d → ℕ → ℂ) (hs : ∀ i, Summable (fun n => ‖f i n‖)) :
    Summable (fun n : Fin d → ℕ => ‖∏ i, f i (n i)‖) ∧
      HasSum (fun n : Fin d → ℕ => ∏ i, f i (n i)) (∏ i, ∑' n, f i n) := by
  induction d with
  | zero =>
    constructor
    · exact Summable.of_finite
    · simpa using (hasSum_fintype (fun n : Fin 0 → ℕ => ∏ i, f i (n i)))
  | succ d ih =>
    let E : (Fin (d+1) → ℕ) ≃ ℕ × (Fin d → ℕ) := (Fin.consEquiv (fun _ => ℕ)).symm
    obtain ⟨hn, hh⟩ := ih (fun i => f i.succ) (fun i => hs i.succ)
    have hp := (hs 0).mul_norm hn
    have he (n : Fin (d+1) → ℕ) :
        (∏ i, f i (n i)) = f 0 (E n).1 * ∏ i, f i.succ ((E n).2 i) := by
      exact Fin.prod_univ_succ _
    constructor
    · have h := hp.comp_injective E.injective
      exact h.congr (fun n => congrArg norm (he n).symm)
    · have h := (hs 0).of_norm.hasSum.mul hh hp.of_norm
      rw [Fin.prod_univ_succ]
      have h' := E.hasSum_iff.mpr h
      exact h'.congr_fun he

theorem complex_finite_product_hasSum (ι : Type*) [Fintype ι]
    (f : ι → ℕ → ℂ) (hs : ∀ i, Summable (fun n => ‖f i n‖)) :
    Summable (fun n : ι → ℕ => ‖∏ i, f i (n i)‖) ∧
      HasSum (fun n : ι → ℕ => ∏ i, f i (n i)) (∏ i, ∑' n, f i n) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E : (Fin (Fintype.card ι) → ℕ) ≃ (ι → ℕ) := e.arrowCongr (Equiv.refl ℕ)
  obtain ⟨hn, hh⟩ := complex_fin_product_hasSum (Fintype.card ι)
    (fun i => f (e i)) (fun i => hs (e i))
  have he (n : Fin (Fintype.card ι) → ℕ) :
      (∏ i, f (e i) (n i)) = ∏ j, f j (E n j) := by
    rw [← e.bijective.prod_comp (fun j => f j (E n j))]
    apply Finset.prod_congr rfl
    intro i _
    simp only [E, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply, e.symm_apply_apply]
  constructor
  · apply E.summable_iff.mp
    exact hn.congr (fun n => congrArg norm (he n))
  · apply E.hasSum_iff.mp
    have hp : (∏ i, ∑' n, f (e i) n) = ∏ j, ∑' n, f j n :=
      e.bijective.prod_comp (fun j => ∑' n, f j n)
    rw [← hp]
    exact hh.congr_fun (fun n => (he n).symm)

end WaringSiegel
