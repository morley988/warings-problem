import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Large samples from a quadratic Gram estimate

A term with coefficient C multiplies the squared coefficient norm.
An entrywise error E multiplies the square of its ℓ¹ norm. At levels
above the square-root of the latter error its contribution is absorbed.
-/

open scoped BigOperators ComplexConjugate
namespace WaringLinear
noncomputable section

/-- The quadratic form of a finite matrix on complex coefficients. -/
def gramForm {ι : Type*} [Fintype ι] (A : ι → ι → ℂ) (w : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (w i)*w j*A i j

/-- An entrywise estimate on the large-conductor Gram summand joins
the operator estimate on the small-conductor summand. -/
theorem synthesis_of_split_gram {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (v : ι → V) (A B : ι → ι → ℂ) (C E : ℝ)
    (hsplit : ∀ i j, inner ℂ (v i) (v j)=A i j+B i j)
    (hsmall : ∀ w, ‖gramForm A w‖ ≤ C*(∑ i, ‖w i‖^2))
    (hlarge : ∀ i j, ‖B i j‖≤E) (w : ι → ℂ) :
    ‖∑ i, w i • v i‖^2 ≤ C*(∑ i, ‖w i‖^2)+E*(∑ i, ‖w i‖)^2 := by
  classical
  let x := ∑ i, w i • v i
  have hid : inner ℂ x x = gramForm A w+gramForm B w := by
    simp only [x,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
      Finset.mul_sum,hsplit, mul_add,Finset.sum_add_distrib,gramForm]
    apply congrArg₂ (·+·) <;> (conv_lhs => rw [Finset.sum_comm]) <;>
      apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;> ring
  have he : ‖x‖^2 = ‖gramForm A w+gramForm B w‖ := by
    rw [←hid,inner_self_eq_norm_sq_to_K,norm_pow]
    change ‖x‖^2 = ‖(‖x‖:ℂ)‖^2
    simp
  have hb : ‖gramForm B w‖ ≤ E*(∑ i, ‖w i‖)^2 := by
    calc
      _ ≤ ∑ i, ‖∑ j, conj (w i)*w j*B i j‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖conj (w i)*w j*B i j‖ := Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i, ∑ j, ‖w i‖*‖w j‖*E := by
        refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
        simp only [norm_mul,RCLike.norm_conj]
        exact mul_le_mul_of_nonneg_left (hlarge i j) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by simp [pow_two,Finset.mul_sum,mul_comm]
  change ‖x‖^2 ≤ _
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (hsmall w) hb)

/-- Hilbert-space weak-L² estimate for the large Fourier samples. -/
theorem gram_large_sample_count {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (v : ι → V) (c : V) (C E Y : ℝ) (hC : 0≤C) (hE : 0≤E) (hY : 0<Y)
    (hGram : ∀ w : ι → ℂ, ‖∑ i, w i • v i‖^2 ≤
      C*(∑ i, ‖w i‖^2)+E*(∑ i, ‖w i‖)^2)
    (hlarge : ∀ i, Y≤‖inner ℂ (v i) c‖)
    (habs : 2*‖c‖^2*E≤Y^2) :
    (Fintype.card ι:ℝ)*Y^2 ≤ 2*C*‖c‖^2 := by
  classical
  let w (i : ι) := inner ℂ (v i) c
  let t : ℝ := ∑ i, ‖w i‖^2
  let j : ℝ := Fintype.card ι
  have ht : 0≤t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hj : 0≤j := Nat.cast_nonneg _
  have hlow : j*Y^2 ≤ t := by
    calc
      j*Y^2 = ∑ _i : ι, Y^2 := by simp [j]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hY.le (hlarge i) 2)
  have hcs : (∑ i, ‖w i‖)^2 ≤ j*t := by
    simpa [j,t] using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖w i‖))
  have hgram := (hGram w).trans (add_le_add_left (mul_le_mul_of_nonneg_left hcs hE) _)
  have hcoef : inner ℂ (∑ i, w i • v i) c = (t:ℂ) := by
    simp only [t,sum_inner,inner_smul_left,Complex.ofReal_sum,Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i _
    exact Complex.conj_mul' (w i)
  have hin := norm_inner_le_norm (𝕜 := ℂ) (∑ i, w i • v i) c
  rw [hcoef,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht] at hin
  have hin' := pow_le_pow_left₀ ht hin 2
  rw [mul_pow] at hin'
  have henergy := hin'.trans (mul_le_mul_of_nonneg_right hgram (sq_nonneg ‖c‖))
  have hupper : t ≤ (C+E*j)*‖c‖^2 := by
    by_cases hz : t=0
    · rw [hz]; positivity
    · have htpos := lt_of_le_of_ne ht (Ne.symm hz)
      apply le_of_mul_le_mul_right _ htpos
      change t*t ≤ ((C+E*j)*‖c‖^2)*t
      change t^2 ≤ (C*t+E*(j*t))*‖c‖^2 at henergy
      linarith only [henergy]
  have hsave := mul_le_mul_of_nonneg_left habs hj
  change j*Y^2≤2*C*‖c‖^2
  nlinarith only [hupper,hlow,hsave]

#print axioms synthesis_of_split_gram
#print axioms gram_large_sample_count
end
end WaringLinear
