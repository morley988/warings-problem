import WaringLinear.GramAbsorption
import WaringLinear.TruncatedSpectrum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # From the finite Gram forms to the squared mass on a fibre
All dyadic levels are supplied from one entrywise absorption threshold.
-/

noncomputable section
open scoped BigOperators Classical
namespace WaringLinear
variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem gram_truncated_fibre (v : ι → V) (c : V) (X C E : ℝ)
    (hX : 0<X) (hC : 0≤C) (hE : 0≤E) (J : ℕ)
    (hupper : ∀ i,‖inner ℂ (v i) c‖≤X)
    (hGram : ∀ (s : Finset ι) (w : s → ℂ),
      ‖∑ i,w i • v i.1‖^2 ≤ C*(∑ i,‖w i‖^2)+E*(∑ i,‖w i‖)^2)
    (habs : 2*‖c‖^2*E≤(X/(2:ℝ)^J)^2) :
    (∑ i∈spectrum (fun i => ‖inner ℂ (v i) c‖/X) J, ‖inner ℂ (v i) c‖^2) ≤
      (1+4*(J:ℝ))*(2*C*‖c‖^2) := by
  classical
  let y (i : ι) := ‖inner ℂ (v i) c‖/X
  have hy (i : ι) : 0≤y i ∧ y i≤1 := ⟨div_nonneg (norm_nonneg _) hX.le,(div_le_one hX).mpr (hupper i)⟩
  let L := 2*C*‖c‖^2
  have hc (j : ℕ) (hj : j≤J) : ((spectrum y j).card:ℝ)≤L/X^2*((2:ℝ)^j)^2 := by
    let s := spectrum y j
    have hjpos : 0<(2:ℝ)^j := by positivity
    have hJpos : 0<(2:ℝ)^J := by positivity
    have hmono : X/(2:ℝ)^J≤X/(2:ℝ)^j :=
      div_le_div_of_nonneg_left hX.le hjpos (pow_le_pow_right₀ (by norm_num) hj)
    have hl (i : s) : X/(2:ℝ)^j≤‖inner ℂ (v i.1) c‖ := by
      have h : 1≤(2:ℝ)^j*(‖inner ℂ (v i.1) c‖/X) := (Finset.mem_filter.mp i.2).2
      apply (div_le_iff₀ hjpos).2
      rw [←mul_div_assoc,(le_div_iff₀ hX)] at h
      linarith only [h]
    have hn := gram_large_sample_count (fun i : s => v i.1) c C E (X/(2:ℝ)^j)
      hC hE (div_pos hX hjpos) (hGram s) hl
      (habs.trans (pow_le_pow_left₀ (div_nonneg hX.le hJpos.le) hmono 2))
    simp only [Fintype.card_coe] at hn
    change (s.card:ℝ)*(X/(2:ℝ)^j)^2 ≤ L at hn
    change (s.card:ℝ) ≤ L/X^2*((2:ℝ)^j)^2
    rw [div_pow,←mul_div_assoc,(div_le_iff₀ (sq_pos_of_pos hjpos))] at hn
    rw [div_mul_eq_mul_div,(le_div_iff₀ (sq_pos_of_pos hX))]
    exact hn
  have hresult := truncated_square_sum y (L/X^2) hy J hc
  have hident : (∑ i∈spectrum y J, ‖inner ℂ (v i) c‖^2)=
      X^2*∑ i∈spectrum y J,(y i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [y]
    rw [div_pow]
    field_simp
  change (∑ i∈spectrum y J, ‖inner ℂ (v i) c‖^2)≤(1+4*(J:ℝ))*L
  rw [hident]
  apply (mul_le_mul_of_nonneg_left hresult (sq_nonneg X)).trans
  apply le_of_eq
  field_simp

#print axioms gram_truncated_fibre
end WaringLinear
