import Waring.PolicyCompletionCongruence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The derivative-zero term in efficient differencing

A bounded-degree nonconstant polynomial has only boundedly many derivative
zeros. For the resulting finite set of auxiliary arguments, finite Cauchy
reduces its mixed collision count to the genuine smooth even moment. All
frequency offsets are retained: no pointwise subsum comparison is used.
-/

noncomputable section
open scoped BigOperators
namespace Waring.DerivativeZeroCount
open AuxiliaryL2Grouping PolicyCompletionCongruence

/-- Equal-class collisions for a Cartesian frequency sum. -/
theorem same_parameter_collisions_card {ι κ : Type*} [DecidableEq ι]
    (A : Finset ι) (B : Finset κ) (F : ι → ℤ) (U : κ → ℤ) :
    (sameClassCollisions (A ×ˢ B) (fun x => F x.1 + U x.2) Prod.fst).card =
      A.card * (collisionPairs B U).card := by
  classical
  let f : ι × (κ × κ) → (ι × κ) × (ι × κ) :=
    fun p => ((p.1,p.2.1),(p.1,p.2.2))
  have hf : Function.Injective f := by
    rintro ⟨a,u,v⟩ ⟨b,x,y⟩ h
    simp only [f,Prod.mk.injEq] at h ⊢
    tauto
  have heq : sameClassCollisions (A ×ˢ B) (fun x => F x.1 + U x.2) Prod.fst =
      (A ×ˢ collisionPairs B U).image f := by
    ext p
    rcases p with ⟨⟨a,u⟩,⟨b,v⟩⟩
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hp,hab⟩
      change a=b at hab
      subst b
      rcases Finset.mem_filter.mp hp with ⟨hp,hfreq⟩
      rcases Finset.mem_product.mp hp with ⟨hau,hav⟩
      refine Finset.mem_image.mpr ⟨(a,u,v),?_,rfl⟩
      refine Finset.mem_product.mpr ⟨(Finset.mem_product.mp hau).1,?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hau).2,(Finset.mem_product.mp hav).2⟩,?_⟩
      exact add_left_cancel hfreq
    · intro hp
      obtain ⟨⟨c,x,y⟩,hcx,hfxy⟩ := Finset.mem_image.mp hp
      rcases Finset.mem_product.mp hcx with ⟨hc,hxy⟩
      rcases Finset.mem_filter.mp hxy with ⟨hxy,hU⟩
      rcases Finset.mem_product.mp hxy with ⟨hx,hy⟩
      simp only [f,Prod.mk.injEq] at hfxy
      rcases hfxy with ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hc,hx⟩,
          Finset.mem_product.mpr ⟨hc,hy⟩⟩,congrArg (fun t => F c+t) hU⟩,rfl⟩
  rw [heq,Finset.card_image_of_injective _ hf,Finset.card_product]

/-- A finite auxiliary family costs its cardinality squared. -/
theorem cartesian_collisions_le {ι κ : Type*} [DecidableEq ι]
    (A : Finset ι) (B : Finset κ) (F : ι → ℤ) (U : κ → ℤ) :
    ((collisionPairs (A ×ˢ B) (fun x => F x.1 + U x.2)).card : ℝ) ≤
      (A.card : ℝ)^2 * ((collisionPairs B U).card : ℝ) := by
  classical
  have hkey : ∀ x ∈ A ×ˢ B, x.1 ∈ A :=
    fun x hx => (Finset.mem_product.mp hx).1
  have hbound := collision_card_le_classes (A ×ˢ B)
    (fun x => F x.1 + U x.2) Prod.fst A hkey
    (D := (A.card : ℝ)) (by positivity) (by
      intro n hn
      have hsub : (((A ×ˢ B).filter (fun x : ι × κ => F x.1 + U x.2=n)).image Prod.fst) ⊆ A := by
        intro a ha
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
        exact hkey x (Finset.mem_filter.mp hx).1
      exact_mod_cast Finset.card_le_card hsub)
  have hsame := sameClassCollisions_card (A ×ˢ B)
    (fun x => F x.1 + U x.2) Prod.fst A hkey
  have hsameR : ((sameClassCollisions (A ×ˢ B)
      (fun x => F x.1 + U x.2) Prod.fst).card : ℝ) =
      ∑ a ∈ A, ((collisionPairs (classFiber (A ×ˢ B) Prod.fst a)
        (fun x : ι × κ => F x.1 + U x.2)).card : ℝ) := by exact_mod_cast hsame
  rw [← hsameR,same_parameter_collisions_card,Nat.cast_mul] at hbound
  simpa only [pow_two,mul_assoc] using hbound

def derivativeZeroArguments {ι : Type*} (C : Finset ι) (Z : Finset ℤ)
    (F : ι → Polynomial ℤ) : Finset (ι × ℤ) := by
  classical
  exact (C ×ˢ Z).filter (fun x => (F x.1).derivative.eval x.2=0)

/-- No dependence on the interval length remains in the derivative-zero set. -/
theorem derivativeZeroArguments_card_le {ι : Type*} [DecidableEq ι]
    (C : Finset ι) (Z : Finset ℤ) (F : ι → Polynomial ℤ) (d : ℕ)
    (hF : ∀ c ∈ C, (F c).derivative ≠ 0 ∧ (F c).derivative.natDegree ≤ d) :
    (derivativeZeroArguments C Z F).card ≤ C.card*d := by
  classical
  let roots := fun c => (Z.filter (fun z => (F c).derivative.eval z=0)).image
    (fun z => (c,z))
  have hsub : derivativeZeroArguments C Z F ⊆ C.biUnion roots := by
    intro x hx
    obtain ⟨hx,hzero⟩ := Finset.mem_filter.mp hx
    rcases Finset.mem_product.mp hx with ⟨hc,hz⟩
    exact Finset.mem_biUnion.mpr ⟨x.1,hc,
      Finset.mem_image.mpr ⟨x.2,Finset.mem_filter.mpr ⟨hz,hzero⟩,rfl⟩⟩
  calc
    _ ≤ (C.biUnion roots).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ C, (roots c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, d := by
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.card_image_le.trans
      apply (Polynomial.card_le_degree_of_subset_roots ?_).trans (hF c hc).2
      intro z hz
      exact (Polynomial.mem_roots (hF c hc).1).mpr (Finset.mem_filter.mp hz).2
    _ = C.card*d := by simp

/-- Source N_s term, with its actual frequency equation and arbitrary tuples. -/
theorem derivativeZero_collisions_le {ι κ : Type*} [DecidableEq ι]
    (C : Finset ι) (Z : Finset ℤ) (F : ι → Polynomial ℤ) (d : ℕ)
    (hF : ∀ c ∈ C, (F c).derivative ≠ 0 ∧ (F c).derivative.natDegree ≤ d)
    (B : Finset κ) (U : κ → ℤ) :
    ((collisionPairs ((derivativeZeroArguments C Z F) ×ˢ B)
      (fun x => (F x.1.1).eval x.1.2 + U x.2)).card : ℝ) ≤
      ((C.card : ℝ)*(d : ℝ))^2 * ((collisionPairs B U).card : ℝ) := by
  have hcard : ((derivativeZeroArguments C Z F).card : ℝ) ≤ (C.card : ℝ)*(d : ℝ) := by
    exact_mod_cast derivativeZeroArguments_card_le C Z F d hF
  exact (cartesian_collisions_le (derivativeZeroArguments C Z F) B
    (fun x => (F x.1).eval x.2) U).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard 2) (by positivity))

/-- Nonconstant characteristic-zero polynomials meet the derivative condition. -/
theorem derivativeZero_collisions_le_of_degree {ι κ : Type*} [DecidableEq ι]
    (C : Finset ι) (Z : Finset ℤ) (F : ι → Polynomial ℤ) (d : ℕ)
    (hF : ∀ c ∈ C, 0 < (F c).natDegree ∧ (F c).natDegree ≤ d)
    (B : Finset κ) (U : κ → ℤ) :
    ((collisionPairs ((derivativeZeroArguments C Z F) ×ˢ B)
      (fun x => (F x.1.1).eval x.1.2 + U x.2)).card : ℝ) ≤
      ((C.card : ℝ)*((d-1 : ℕ) : ℝ))^2 * ((collisionPairs B U).card : ℝ) := by
  apply derivativeZero_collisions_le C Z F (d-1) _ B U
  intro c hc
  refine ⟨?_,(Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right (hF c hc).2 1)⟩
  intro hzero
  have hz := Polynomial.natDegree_eq_zero_of_derivative_eq_zero hzero
  have hpos := (hF c hc).1
  omega

#print axioms cartesian_collisions_le
#print axioms derivativeZero_collisions_le_of_degree
end Waring.DerivativeZeroCount
