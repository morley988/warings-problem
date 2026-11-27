import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! # Completion and the dual frequency tails in the rational B-process -/
noncomputable section
open scoped BigOperators Classical
namespace WaringLinear
variable {q : ℕ} [NeZero q]

/-- Exact Poisson completion for any finite weighted set of integer nodes
and an arbitrary periodic phase. Each complete sum has the genuine
additive inverse-transform sign and the normalization q^{-1}. -/
theorem weighted_rational_completion {α:Type*} [Fintype α]
    (node : α→ZMod q) (w:α→ℂ) (f:ZMod q→ℂ) :
    ∑x,w x*f (node x) =
      (q:ℂ)⁻¹*∑b:ZMod q,ZMod.dft f b*∑x,w x*ZMod.stdAddChar (b*node x) := by
  have inv (y:ZMod q) : f y=(q:ℂ)⁻¹*∑b:ZMod q,ZMod.stdAddChar (b*y)*ZMod.dft f b := by
    have H := congrFun (ZMod.dft.symm_apply_apply f) y
    rw [ZMod.invDFT_apply] at H
    exact H.symm
  calc
    _ = ∑x,(q:ℂ)⁻¹*∑b:ZMod q,ZMod.dft f b*(w x*ZMod.stdAddChar (b*node x)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [inv (node x),mul_left_comm (w x) (q:ℂ)⁻¹]
      apply congrArg
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]

def cyclicDifference (f:ZMod q→ℂ) (x:ZMod q) := f (x+1)-f x

/-- A shift of a periodic smooth cutoff becomes the exact linear
difference multiplier on the dual conductor. -/
theorem dft_cyclicDifference (f:ZMod q→ℂ) (b:ZMod q) :
    ZMod.dft (cyclicDifference f) b=(ZMod.stdAddChar b-1)*ZMod.dft f b := by
  simp only [ZMod.dft_apply,cyclicDifference,smul_eq_mul,mul_sub,Finset.sum_sub_distrib,sub_mul,one_mul]
  apply congrArg (fun x:ℂ => x-∑j:ZMod q,ZMod.stdAddChar (-(j*b))*f j)
  let g (j:ZMod q) := ZMod.stdAddChar (-(j*b))*f j
  calc
    _ = ∑j:ZMod q,ZMod.stdAddChar b*g (j+1) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp [g]
      rw [←mul_assoc,←AddChar.map_add_eq_mul,show b+-((j+1)*b)= -(j*b) by ring]
    _ = _ := by
      rw [←Finset.mul_sum]
      exact congrArg _ (Equiv.sum_comp (Equiv.addRight (1:ZMod q)) g)

/-- Repeated finite summation by parts costs the L1 norm of the actual
differenced cutoff and an explicit power of the frequency divisor. -/
theorem completed_tail_bound (f:ZMod q→ℂ) (b:ZMod q) (L:ℕ) (hb:b≠0) :
    ‖ZMod.dft f b‖ ≤ (∑x:ZMod q,‖((cyclicDifference (q:=q))^[L] f) x‖)/
      ‖ZMod.stdAddChar b-1‖^L := by
  have id (j:ℕ) : ZMod.dft ((cyclicDifference (q:=q))^[j] f) b =
      (ZMod.stdAddChar b-1)^j * ZMod.dft f b := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply',dft_cyclicDifference,ih,pow_succ]
      ring
  have hn : ZMod.stdAddChar b≠1 := by
    intro h
    apply hb
    apply ZMod.injective_stdAddChar
    simpa using h
  apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn)) _)).mpr
  calc
    _ = ‖(ZMod.stdAddChar b-1)^L * ZMod.dft f b‖ := by simp [mul_comm]
    _ = ‖ZMod.dft ((cyclicDifference (q:=q))^[L] f) b‖ := congrArg _ (id L).symm
    _ ≤ _ := by
      rw [ZMod.dft_apply]
      exact (norm_sum_le _ _).trans (by simp [smul_eq_mul,ZMod.stdAddChar_apply])

#print axioms weighted_rational_completion
#print axioms completed_tail_bound
end WaringLinear
