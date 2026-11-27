import WaringLinear.PolynomialStationary
import WaringLinear.FiniteLocalInverse

/-! # Exact detection of a nondegenerate critical congruence -/
noncomputable section
namespace WaringLinear
open Polynomial IsLocalRing
open scoped Classical BigOperators
variable {A : Type*} [CommRing A] [IsLocalRing A] [Fintype A]

theorem stationary_simple_coset_sum (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive)
    (f : A[X]) (c d a : A) (hc : c^2=0) (hd : residue A d=0)
    (hann : ∀ x : A, c*x=0 ↔ x∈Ideal.span {d})
    (hroot : f.derivative.eval a=0) (hder : IsUnit (f.derivative.derivative.eval a)) :
    (∑ x ∈ Finset.univ.filter (fun x : A => residue A x=residue A a), ψ (f.eval x)) =
      ∑ x ∈ Finset.univ.filter (fun x : A => x-a∈Ideal.span {d}), ψ (f.eval x) := by
  have hres : residue A c=0 := by
    have h : (residue A c)^2=0 := by rw [←map_pow,hc,map_zero]
    exact (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp h
  let S := Finset.univ.filter (fun x : A => residue A x=residue A a)
  let w (x : A) : ℂ := if x∈S then 1 else 0
  have hS (x t : A) : x+c*t∈S ↔ x∈S := by simp [S,map_add,map_mul,hres]
  have hw (x t : A) : w (x+c*t)=w x := by simp only [w,hS]
  have hfactor (x : A) : (x-a)*polynomialDifference f.derivative a (x-a)=f.derivative.eval x := by
    simpa only [show a+(x-a)=x by abel,hroot,sub_zero] using
      mul_polynomialDifference f.derivative a (x-a)
  have hcrit (x : A) : x∈S ∧ c*f.derivative.eval x=0 ↔ x-a∈Ideal.span {d} := by
    constructor
    · rintro ⟨hx,hf⟩
      have hu := simple_difference_unit f.derivative (Finset.mem_filter.mp hx).2 hder
      apply (hann _).1
      apply hu.mul_left_inj.mp
      rw [zero_mul,mul_assoc,hfactor,hf]
    · intro h
      obtain ⟨t,ht⟩ := Ideal.mem_span_singleton.mp h
      have hx := congrArg (residue A) ht
      simp only [map_sub,map_mul,hd,zero_mul,sub_eq_zero] at hx
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,?_⟩
      rw [←hfactor,←mul_assoc,(hann _).2 h,zero_mul]
  have filtered := weighted_polynomial_stationary_filter ψ hψ f c hc w hw
  change (∑ x∈S, ψ (f.eval x)) = _
  calc
    _ = ∑ x : A, w x*ψ (f.eval x) := by
      simp only [w,ite_mul,one_mul,zero_mul,←Finset.sum_filter]; simp
    _ = _ := filtered
    _ = _ := by
      simp only [Finset.sum_filter,w,ite_mul,one_mul,zero_mul]
      apply Finset.sum_congr rfl
      intro x _
      have h := hcrit x
      split_ifs <;> tauto

#print axioms stationary_simple_coset_sum
end WaringLinear
