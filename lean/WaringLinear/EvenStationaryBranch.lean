import WaringLinear.PolynomialStationary
import WaringLinear.FiniteLocalInverse
import WaringLinear.HalfIdealCard

/-! # Exact even-conductor stationary phase on a simple branch -/
noncomputable section
namespace WaringLinear
open Polynomial IsLocalRing
open scoped Classical BigOperators
variable {A : Type*} [CommRing A] [IsLocalRing A] [Fintype A]

/-- A critical point in the residue field with unit second derivative has
a unique lift on its branch. Its additive character is the exact phase;
the amplitude is the square root of the order of the finite ring. -/
theorem even_stationary_branch (ψ : AddChar A ℂ) (hψ : ψ.IsPrimitive)
    (f : A[X]) (c y : A) (hann : ∀ x : A, c*x=0 ↔ x∈Ideal.span {c})
    (hy : residue A (f.derivative.eval y)=0) (hder : IsUnit (f.derivative.derivative.eval y)) :
    ∃ a : A, residue A a=residue A y ∧ f.derivative.eval a=0 ∧
      (∑ x ∈ Finset.univ.filter (fun x : A => residue A x=residue A y), ψ (f.eval x)) =
        (Real.sqrt (Fintype.card A):ℂ)*ψ (f.eval a) := by
  obtain ⟨a,⟨ha,hroot⟩,_⟩ := finite_local_inverse f.derivative y 0 hder (by simpa using hy.symm)
  refine ⟨a,ha,hroot,?_⟩
  have hc : c^2=0 := by rw [pow_two]; exact (hann c).2 (Ideal.subset_span (Set.mem_singleton _))
  have hres : residue A c=0 := by
    have h : (residue A c)^2=0 := by rw [←map_pow,hc,map_zero]
    exact pow_eq_zero_iff (by decide : (2:ℕ)≠0) |>.mp h
  let S := Finset.univ.filter (fun x : A => residue A x=residue A y)
  have hS (x t : A) : x+c*t∈S ↔ x∈S := by simp [S,map_add,map_mul,hres]
  have hu : IsUnit (f.derivative.derivative.eval a) := (residue_ne_zero_iff_isUnit _).1
    ((eval_same_residue f.derivative.derivative ha) ▸ (residue_ne_zero_iff_isUnit _).2 hder)
  have hd (x : A) : (x-a)*polynomialDifference f.derivative a (x-a)=f.derivative.eval x := by
    simpa only [show a+(x-a)=x by abel,hroot,sub_zero] using
      mul_polynomialDifference f.derivative a (x-a)
  have hcrit (x : A) : x∈S ∧ c*f.derivative.eval x=0 ↔ x-a∈Ideal.span {c} := by
    constructor
    · rintro ⟨hx,hf⟩
      have he := (Finset.mem_filter.mp hx).2
      have hu' := simple_difference_unit f.derivative (he.trans ha.symm) hu
      apply (hann _).1
      apply hu'.mul_left_inj.mp
      rw [zero_mul,mul_assoc,hd,hf]
    · intro h
      obtain ⟨t,ht⟩ := Ideal.mem_span_singleton.mp h
      have hresx := congrArg (residue A) ht
      simp only [map_sub,map_mul,hres,zero_mul,sub_eq_zero] at hresx
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hresx.trans ha⟩,?_⟩
      rw [←hd,←mul_assoc,(hann _).2 h,zero_mul]
  have e := stationary_single_coset ψ hψ f c a hc S hS hcrit
  have hcard := sqrt_card_self_annihilating_ideal c hann
  change (∑ x∈S, ψ (f.eval x)) = _
  rw [e,←hcard]
  norm_cast

#print axioms even_stationary_branch
end WaringLinear
