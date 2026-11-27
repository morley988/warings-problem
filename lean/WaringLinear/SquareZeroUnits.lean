import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic

/-! # Principal units in a square-zero ideal

Multiplication of principal units becomes addition of their deviations from one.
The last statements give a one-summand correction for a sum of kth powers.
-/

namespace WaringLinear
variable {R : Type*} [CommRing R]

private theorem mul_zero_of_mem_squareZero {I : Ideal R} (hI : I*I = ⊥)
    {a b : R} (ha : a ∈ I) (hb : b ∈ I) : a*b = 0 := by
  have h := Ideal.mul_mem_mul ha hb
  rwa [hI, Ideal.mem_bot] at h

private theorem principal_unit_deviations_add (I : Ideal R) (hI : I*I = ⊥)
    (U : Subgroup Rˣ) (hU : ∀ u ∈ U, (u : R)-1 ∈ I)
    (u v : Rˣ) (hu : u ∈ U) (hv : v ∈ U) :
    ((u*v : Rˣ) : R)-1 = ((u : R)-1)+((v : R)-1) := by
  have h := mul_zero_of_mem_squareZero hI (hU u hu) (hU v hv)
  push_cast
  linear_combination h

/-- The deviations of the members of a principal unit subgroup form an
additive subgroup in a square-zero ideal. -/
def unitDeviations (I : Ideal R) (hI : I*I = ⊥) (U : Subgroup Rˣ)
    (hU : ∀ u ∈ U, (u : R)-1 ∈ I) : AddSubgroup R where
  carrier := {x | ∃ u ∈ U, (u : R)-1=x}
  zero_mem' := ⟨1,U.one_mem,by simp⟩
  add_mem' := by
    rintro _ _ ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩
    exact ⟨u*v,U.mul_mem hu hv,principal_unit_deviations_add I hI U hU u v hu hv⟩
  neg_mem' := by
    rintro _ ⟨u,hu,rfl⟩
    refine ⟨u⁻¹,U.inv_mem hu,?_⟩
    have h := principal_unit_deviations_add I hI U hU u u⁻¹ hu (U.inv_mem hu)
    simp only [mul_inv_cancel, Units.val_one, sub_self] at h
    linear_combination -h

/-- A deviation that is itself represented by a kth-power unit may be absorbed
by changing a single kth-power summand. -/
theorem kth_unit_coset_correction (I : Ideal R) (hI : I*I = ⊥)
    (U : Subgroup Rˣ) (hU : ∀ u ∈ U, (u : R)-1 ∈ I)
    (k : ℕ) (hPow : ∀ u ∈ U, ∃ v : Rˣ, v^k=u)
    (y : Rˣ) {z : R} (hz : z ∈ unitDeviations I hI U hU) :
    ∃ w : Rˣ, (w:R)^k = (y:R)^k+(y:R)^k*z := by
  obtain ⟨u,hu,rfl⟩ := hz
  obtain ⟨v,rfl⟩ := hPow u hu
  refine ⟨y*v,?_⟩
  push_cast
  ring

/-- The correction also preserves the number and unit nature of the summands. -/
theorem sum_kth_units_coset_correction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (hI : I*I = ⊥) (U : Subgroup Rˣ)
    (hU : ∀ u ∈ U, (u : R)-1 ∈ I) (k : ℕ)
    (hPow : ∀ u ∈ U, ∃ v : Rˣ, v^k=u)
    (y : ι → Rˣ) (i : ι) {z : R} (hz : z ∈ unitDeviations I hI U hU) :
    ∃ w : ι → Rˣ, (∑ j, (w j : R)^k) =
      (∑ j, (y j : R)^k) + (y i : R)^k*z := by
  obtain ⟨v,hv⟩ := kth_unit_coset_correction I hI U hU k hPow (y i) hz
  refine ⟨Function.update y i v,?_⟩
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add (s := Finset.univ) (f := fun j => (y j : R)^k)
      (Finset.mem_univ i), Function.update_self, hv]
  have hsame : (∑ j ∈ Finset.univ.erase i, ((Function.update y i v) j : R)^k) =
      ∑ j ∈ Finset.univ.erase i, (y j : R)^k :=
    Finset.sum_congr rfl (fun _ hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  rw [hsame,add_assoc]

#print axioms unitDeviations
#print axioms kth_unit_coset_correction
#print axioms sum_kth_units_coset_correction
end WaringLinear
