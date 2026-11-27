import WaringSiegel.WSL2LocalGoodPrime
import Mathlib.Algebra.Ring.GeomSum

/-!
# Genuine Hensel lifting for every positive power away from that exponent

These are actual lifts in a Henselian local ring. The sole good-prime
condition is that the integer exponent is a unit. No residue-field count
or local lifting assertion is assumed.
-/
noncomputable section
set_option maxHeartbeats 800000
open Polynomial IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3

theorem power_lift_of_nonzero_residue
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (k : ℕ) (hk : 0<k) (hku : IsUnit (k:R)) {a : R} {x : ResidueField R}
    (hx : x^k=residue R a) (hx0 : x≠0) :
    ∃ y : R, y^k=a ∧ residue R y=x ∧ IsUnit y := by
  let f : R[X] := X^k-C a
  have hf : f.Monic := monic_X_pow_sub_C a hk.ne'
  have hroot : aeval x f=0 := by simp [f,hx]
  have hkr : (k:ResidueField R)≠0 := by
    simpa only [map_natCast] using (hku.map (residue R)).ne_zero
  have hder : aeval x f.derivative≠0 := by
    have he : aeval x f.derivative=(k:ResidueField R)*x^(k-1) := by
      simp [f,derivative_pow]
    rw [he]
    exact mul_ne_zero hkr (pow_ne_zero _ hx0)
  have hH := ((HenselianLocalRing.TFAE R).out 0 1).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨y,hy,hyr⟩ := hH f hf x hroot hder
  refine ⟨y,?_,hyr,(residue_ne_zero_iff_isUnit y).mp (hyr ▸ hx0)⟩
  exact sub_eq_zero.mp (by simpa [f,Polynomial.IsRoot] using hy)

theorem power_sum_adjust_free_coordinates
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (k : ℕ) (hk : 0<k) (hku : IsUnit (k:R))
    {s : ℕ} (x : Fin (s+1) → R) (hx : IsUnit (x 0))
    (y : Fin s → R) (hy : ∀ i, y i-x i.succ∈maximalIdeal R) :
    ∃ z : R, z^k+∑ i,y i^k=∑ i,x i^k ∧ IsUnit z := by
  let a : R := (∑ i,x i^k)-∑ i,y i^k
  have hres (i : Fin s) : residue R (y i)=residue R (x i.succ) :=
    Ideal.Quotient.eq.mpr (hy i)
  have hr : (residue R (x 0))^k=residue R a := by
    simp only [a,map_sub,map_add,map_sum,map_pow,hres,Fin.sum_univ_succ]
    abel
  obtain ⟨z,hz,-,hzu⟩ := power_lift_of_nonzero_residue k hk hku hr
    ((residue_ne_zero_iff_isUnit _).mpr hx)
  exact ⟨z,eq_sub_iff_add_eq.mp hz,hzu⟩

theorem power_tuple_unit_first
    {R : Type*} [CommRing R] (k : ℕ) {s : ℕ} {a : R}
    (h : ∃ x : Fin (s+1) → R, (∑ i,x i^k)=a ∧ ∃ i,IsUnit (x i)) :
    ∃ x : Fin (s+1) → R, (∑ i,x i^k)=a ∧ IsUnit (x 0) := by
  classical
  obtain ⟨x,hx,j,hj⟩ := h
  let e : Fin (s+1) ≃ Fin (s+1) := Equiv.swap 0 j
  refine ⟨fun i => x (e i),(Equiv.sum_comp e (fun i => x i^k)).trans hx,?_⟩
  simpa [e] using hj

theorem power_tuple_lift_of_nonzero_residue
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (k : ℕ) (hk : 0<k) (hku : IsUnit (k:R)) {s : ℕ} {a : R}
    (x : Fin s → ResidueField R) (hsum : (∑ i,x i^k)=residue R a)
    (hunit : ∃ i,x i≠0) :
    ∃ y : Fin s → R, (∑ i,y i^k)=a ∧ ∃ i,IsUnit (y i) := by
  classical
  choose y hy using (fun i => residue_surjective (x i))
  obtain ⟨j,hj⟩ := hunit
  let b : R := a-∑ i∈Finset.univ.erase j,y i^k
  have hb : x j^k=residue R b := by
    simp only [b,map_sub,map_sum,map_pow,hy]
    rw [← hsum,← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    abel
  obtain ⟨z,hz,-,hzu⟩ := power_lift_of_nonzero_residue k hk hku hb hj
  refine ⟨Function.update y j z,?_,j,?_⟩
  · have hpow : (fun i => (Function.update y j z i)^k)=
        Function.update (fun i => y i^k) j (z^k) := by
      ext i
      by_cases h : i=j <;> simp only [Function.update_apply,h,if_true,if_false]
    rw [hpow,Finset.sum_update_of_mem (Finset.mem_univ j),hz]
    simp only [b,Finset.sdiff_singleton_eq_erase]
    abel
  · simpa using hzu

#print axioms power_lift_of_nonzero_residue
#print axioms power_sum_adjust_free_coordinates
#print axioms power_tuple_lift_of_nonzero_residue
end WaringSiegel.WSL3
