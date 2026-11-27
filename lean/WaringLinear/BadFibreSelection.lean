import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-! # Coefficient selection on exceptional fibres

The sets S(i) are the roots divisible by the specified marked prime. When
the roots coprime to the whole selected product make a small exponential
sum, inclusion–exclusion selects one nonempty divisor with a large sum.
-/

open scoped BigOperators
namespace WaringLinear
noncomputable section
open Finset

theorem bad_fibre_selection {α ι : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq ι] (s : Finset ι) (S : ι → Finset α) (f : α → ℂ)
    (hbad : 2*‖∑ n ∈ (s.biUnion S)ᶜ, f n‖ < ‖∑ n, f n‖) :
    ∃ t ∈ s.powerset, t.Nonempty ∧
      ‖∑ n, f n‖ ≤ 2*((2:ℝ)^s.card)*‖∑ n ∈ t.inf S, f n‖ := by
  classical
  let E := s.powerset.filter (·.Nonempty)
  let V (t : E) := ∑ n ∈ t.1.inf S, f n
  have hmix :
      ‖∑ n ∈ s.biUnion S, f n‖ ≤ ∑ t : E, ‖V t‖ := by
    rw [Finset.inclusion_exclusion_sum_biUnion s S f]
    calc
      _ ≤ _ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _
        simp [V, Finset.inf'_eq_inf]
  have hadd : (∑ n ∈ (s.biUnion S)ᶜ, f n) + (∑ n ∈ s.biUnion S, f n) = ∑ n, f n :=
    Finset.sum_compl_add_sum _ _
  have htri := norm_add_le (∑ n ∈ (s.biUnion S)ᶜ, f n) (∑ n ∈ s.biUnion S, f n)
  rw [hadd] at htri
  have htotal : ‖∑ n, f n‖<2*∑ t : E, ‖V t‖ := by linarith
  have hNE : (Finset.univ : Finset E).Nonempty := by
    by_contra! hz
    rw [Finset.not_nonempty_iff_eq_empty.mp hz] at htotal
    simp only [Finset.sum_empty,mul_zero,not_lt_of_ge (norm_nonneg _)] at htotal
  obtain ⟨t,_,ht⟩ := Finset.exists_max_image Finset.univ (fun t : E => ‖V t‖) hNE
  have hup : (∑ u : E, ‖V u‖) ≤ (E.card:ℝ)*‖V t‖ := by
    calc
      _ ≤ ∑ _u : E, ‖V t‖ := Finset.sum_le_sum (fun u hu => ht u hu)
      _ = _ := by simp
  have hnum : E.card ≤ 2^s.card := by simpa [E] using (Finset.card_filter_le (s := s.powerset) (·.Nonempty))
  have hnum' : (E.card:ℝ) ≤ (2:ℝ)^s.card := by exact_mod_cast hnum
  have hmax := hup.trans (mul_le_mul_of_nonneg_right hnum' (norm_nonneg _))
  refine ⟨t.1, (Finset.mem_filter.mp t.2).1, (Finset.mem_filter.mp t.2).2, ?_⟩
  change ‖∑ n, f n‖ ≤ 2*(2:ℝ)^s.card*‖V t‖
  linarith only [htotal,hmax]

#print axioms bad_fibre_selection
end
end WaringLinear
