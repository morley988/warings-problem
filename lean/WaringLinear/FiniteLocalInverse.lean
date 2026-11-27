import WaringLinear.PolynomialDifference
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Data.Fintype.Card

/-! # A simple polynomial branch on a finite local ring

A polynomial with unit derivative maps a residue class bijectively onto its
image residue class. The argument uses the integral divided difference and
finiteness. It works equally in ramified and unramified finite local rings.
-/
noncomputable section
namespace WaringLinear
open Polynomial IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A]

theorem eval_same_residue (g : A[X]) {x y : A} (h : residue A x=residue A y) :
    residue A (g.eval x)=residue A (g.eval y) := by
  rw [← g.eval₂_at_apply (residue A) x,← g.eval₂_at_apply (residue A) y,h]

theorem simple_difference_unit (g : A[X]) {x y : A}
    (hres : residue A x=residue A y) (hunit : IsUnit (g.derivative.eval y)) :
    IsUnit (polynomialDifference g y (x-y)) := by
  apply (residue_ne_zero_iff_isUnit _).1
  rw [map_polynomialDifference_eq_derivative (residue A) g y (x-y)
    (by rw [map_sub,hres,sub_self])]
  exact (residue_ne_zero_iff_isUnit _).2 hunit

theorem polynomial_injective_on_simple_branch (g : A[X]) (x₀ : A)
    (hunit : IsUnit (g.derivative.eval x₀)) {x y : A}
    (hx : residue A x=residue A x₀) (hy : residue A y=residue A x₀)
    (heq : g.eval x=g.eval y) : x=y := by
  have hu : IsUnit (g.derivative.eval y) := (residue_ne_zero_iff_isUnit _).1
    ((eval_same_residue g.derivative hy) ▸ (residue_ne_zero_iff_isUnit _).2 hunit)
  have hd := simple_difference_unit g (hx.trans hy.symm) hu
  have hdiff := mul_polynomialDifference g y (x-y)
  rw [show y+(x-y)=x by abel,heq,sub_self] at hdiff
  exact sub_eq_zero.mp (hd.mul_left_inj.mp (hdiff.trans (zero_mul _).symm))

theorem finite_local_inverse [Finite A] (g : A[X]) (x₀ b : A)
    (hunit : IsUnit (g.derivative.eval x₀)) (hb : residue A b=residue A (g.eval x₀)) :
    ∃! x : A, residue A x=residue A x₀ ∧ g.eval x=b := by
  classical
  let S := {x : A // residue A x=residue A x₀}
  let F (x : S) : S := ⟨g.eval (x:A)-g.eval x₀+x₀,by
    rw [map_add,map_sub,eval_same_residue g x.2,sub_self,zero_add]⟩
  have inj : Function.Injective F := by
    intro x y h
    have h₁ : g.eval (x:A)-g.eval x₀+x₀=g.eval (y:A)-g.eval x₀+x₀ := congrArg Subtype.val h
    have h₂ : g.eval (x:A)=g.eval (y:A) := sub_left_inj.mp (add_right_cancel h₁)
    exact Subtype.ext (polynomial_injective_on_simple_branch g x₀ hunit x.2 y.2 h₂)
  let y : S := ⟨b-g.eval x₀+x₀,by simp only [map_add,map_sub,hb,sub_self,zero_add]⟩
  obtain ⟨x,h⟩ := Finite.surjective_of_injective inj y
  have h₁ : g.eval (x:A)-g.eval x₀+x₀=b-g.eval x₀+x₀ := congrArg Subtype.val h
  have h₂ : g.eval (x:A)=b := sub_left_inj.mp (add_right_cancel h₁)
  exact ⟨x,⟨x.2,h₂⟩,fun a ha => polynomial_injective_on_simple_branch g x₀ hunit ha.1 x.2
    (ha.2.trans h₂.symm)⟩

#print axioms polynomial_injective_on_simple_branch
#print axioms finite_local_inverse
end WaringLinear
