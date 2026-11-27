import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Abel

/-! # Weighted parametrization of principal cosets and half-conductor fibres -/
noncomputable section
namespace WaringLinear
open scoped Classical BigOperators
variable {A : Type*} [CommRing A] [Fintype A]

theorem affine_principal_fibre_sum {B : Type*} [Semiring B] (a d : A) (w : A → B) :
    (∑ t : A, w (a+d*t)) =
      ((Finset.univ.filter (fun t : A => d*t=0)).card:B)*
        ∑ x∈Finset.univ.filter (fun x : A => x-a∈Ideal.span {d}), w x := by
  classical
  let f : A →+ A := AddMonoidHom.mulLeft d
  have fibre (x : A) (hx : x-a∈Ideal.span {d}) :
      (Finset.univ.filter (fun t : A => a+d*t=x)).card=
        (Finset.univ.filter (fun t : A => d*t=0)).card := by
    have hset : Finset.univ.filter (fun t : A => a+d*t=x)=
        Finset.univ.filter (fun t : A => d*t=x-a) := by
      ext t
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun h => by rw [←h]; abel,fun h => by rw [h]; abel⟩
    rw [hset]
    obtain ⟨y,hy⟩ := Ideal.mem_span_singleton.mp hx
    exact AddMonoidHom.card_fiber_eq_of_mem_range f ⟨y,hy.symm⟩ ⟨0,map_zero f⟩
  rw [← Finset.sum_fiberwise' Finset.univ (fun t : A => a+d*t) w,Finset.mul_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x-a∈Ideal.span {d}
  · simp [h,fibre x h,nsmul_eq_mul]
  · have hemp : Finset.univ.filter (fun t : A => a+d*t=x)=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      apply h
      have hx := (Finset.mem_filter.mp ht).2
      exact Ideal.mem_span_singleton.mpr ⟨t,by rw [←hx]; abel⟩
    simp [hemp,h]

theorem card_annihilator_squared_of_kernel_in_image (d : A)
    (h : ∀ x : A, d*x=0 → x∈Ideal.span {d}) :
    (Finset.univ.filter (fun x : A => d^2*x=0)).card =
      (Finset.univ.filter (fun x : A => d*x=0)).card^2 := by
  let w (x : A) : ℕ := if d*x=0 then 1 else 0
  have e := affine_principal_fibre_sum (0:A) d w
  simp only [zero_add,sub_zero,w,←mul_assoc,←pow_two,←Finset.sum_filter,
    Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id] at e
  have he : (Finset.univ.filter (fun x : A => x∈Ideal.span {d})).filter (fun x => d*x=0) =
      Finset.univ.filter (fun x : A => d*x=0) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨And.right,fun hx => ⟨h x hx,hx⟩⟩
  simpa only [he,pow_two] using e

#print axioms affine_principal_fibre_sum
#print axioms card_annihilator_squared_of_kernel_in_image
end WaringLinear
