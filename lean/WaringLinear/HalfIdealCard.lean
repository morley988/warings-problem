import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Real.Sqrt

/-! # The middle ideal of a finite ring of even conductor -/
noncomputable section
namespace WaringLinear
open scoped Classical
variable {A : Type*} [CommRing A] [Fintype A]

theorem card_self_annihilating_ideal (c : A)
    (hann : ∀ x : A, c*x=0 ↔ x∈Ideal.span {c}) :
    Fintype.card (Ideal.span {c}:Ideal A)^2=Fintype.card A := by
  let I : Ideal A := Ideal.span {c}
  let H : AddSubgroup A := I.toAddSubgroup
  let f : A →+ A := AddMonoidHom.mulLeft c
  have hk : f.ker=H := by
    ext x
    exact hann x
  have hr : f.range=H := by
    ext x
    change (∃ y : A, c*y=x) ↔ x∈Ideal.span {c}
    rw [Ideal.mem_span_singleton]
    exact exists_congr (fun _ => eq_comm)
  have h := f.ker.card_mul_index
  rw [AddSubgroup.index_ker,hk,hr] at h
  simpa only [pow_two,Nat.card_eq_fintype_card] using h

theorem sqrt_card_self_annihilating_ideal (c : A)
    (hann : ∀ x : A, c*x=0 ↔ x∈Ideal.span {c}) :
    (Fintype.card (Ideal.span {c}:Ideal A):ℝ)=Real.sqrt (Fintype.card A) := by
  have h : (Fintype.card (Ideal.span {c}:Ideal A):ℝ)^2=(Fintype.card A:ℝ) := by
    exact_mod_cast card_self_annihilating_ideal c hann
  rw [← h,Real.sqrt_sq (Nat.cast_nonneg _)]

#print axioms card_self_annihilating_ideal
#print axioms sqrt_card_self_annihilating_ideal
end WaringLinear
