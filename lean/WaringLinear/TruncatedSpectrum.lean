import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # From a weak square bound to a truncated square sum

At a dyadic amplitude the number of large Fourier samples is at most the
inverse square of that amplitude times B. The truncated sum of squares
loses at most four times B per dyadic interval.
-/

namespace WaringLinear
open scoped BigOperators

noncomputable def spectrum {ι : Type*} [Fintype ι] (v : ι → ℝ) (j : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 1 ≤ (2:ℝ)^j*v i)

theorem truncated_square_sum {ι : Type*} [Fintype ι] (v : ι → ℝ) (B : ℝ)
    (hv : ∀ i, 0≤v i ∧ v i≤1) (J : ℕ)
    (hcount : ∀ j≤J, ((spectrum v j).card:ℝ)≤B*((2:ℝ)^j)^2) :
    ∑ i ∈ spectrum v J, (v i)^2 ≤ (1+4*(J:ℝ))*B := by
  classical
  induction J with
  | zero =>
    have h := hcount 0 le_rfl
    simp only [pow_zero,one_pow,mul_one] at h
    calc
      _ ≤ ∑ _i ∈ spectrum v 0, (1:ℝ) := Finset.sum_le_sum (fun i _ => by
        simpa using pow_le_pow_left₀ (hv i).1 (hv i).2 2)
      _ ≤ _ := by simpa using h
  | succ j ih =>
    let E := spectrum v (j+1) \ spectrum v j
    have hprev := ih (fun n h => hcount n (by omega))
    have hsub : spectrum v j ⊆ spectrum v (j+1) := by
      intro i hi
      have hi' : 1≤(2:ℝ)^j*v i := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
      rw [pow_succ]
      linarith only [hi']
    have hpos : 0<(2:ℝ)^j := by positivity
    have he (i) (hi : i ∈ E) : (v i)^2 ≤ 1/((2:ℝ)^j)^2 := by
      have hn := (Finset.mem_sdiff.mp hi).2
      have hlt : (2:ℝ)^j*v i < 1 := by
        apply lt_of_not_ge
        exact fun hh => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
      have hv' : v i ≤ 1/(2:ℝ)^j := by
        apply (le_div_iff₀ hpos).2
        simpa [mul_comm] using hlt.le
      simpa only [div_pow,one_pow] using pow_le_pow_left₀ (hv i).1 hv' 2
    have hcard : (E.card:ℝ) ≤ B*((2:ℝ)^(j+1))^2 := by
      have hE : E⊆spectrum v (j+1) := Finset.sdiff_subset
      exact (show (E.card:ℝ)≤(spectrum v (j+1)).card by exact_mod_cast Finset.card_le_card hE).trans
        (hcount _ le_rfl)
    have hnew : ∑ i ∈ E, (v i)^2 ≤ 4*B := by
      calc
        _ ≤ ∑ _i ∈ E, 1/((2:ℝ)^j)^2 := Finset.sum_le_sum he
        _ = (E.card:ℝ)/((2:ℝ)^j)^2 := by simp [div_eq_mul_inv]
        _ ≤ B*((2:ℝ)^(j+1))^2/((2:ℝ)^j)^2 := div_le_div_of_nonneg_right hcard (sq_nonneg _)
        _ = 4*B := by rw [pow_succ]; field_simp; ring
    have hs := Finset.sum_sdiff hsub (f := fun i => (v i)^2)
    change (∑ i ∈ E, (v i)^2) + (∑ i ∈ spectrum v j, (v i)^2) = _ at hs
    rw [←hs]
    push_cast
    linarith only [hnew,hprev]

#print axioms truncated_square_sum
end WaringLinear
