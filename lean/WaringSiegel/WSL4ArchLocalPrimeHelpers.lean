import WaringSiegel.WSL4ArchLocalTuples
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Basic

/-! # The exact local-prime split and the final unit-coordinate adapter -/
noncomputable section
open scoped BigOperators
open IsLocalRing
namespace WaringSiegel.WSL4

theorem residue_charP_of_prime_not_isUnit
    {R : Type*} [CommRing R] [IsLocalRing R] (k : ℕ) (hk : Nat.Prime k)
    (hku : ¬IsUnit (k:R)) : CharP (ResidueField R) k := by
  apply (CharP.charP_iff_prime_eq_zero hk).mpr
  have h := (residue_ne_zero_iff_isUnit (k:R)).not.mpr hku
  simpa only [map_natCast,not_not] using h

theorem unit_power_tuple_of_short_list
    {R : Type*} [CommRing R] (k : ℕ) (hk : 0<k) {s : ℕ} {a : R}
    (l : List R) (hlen : l.length+1≤s) (hl : localPowerListSum k l=a-1) :
    ∃x : Fin s → R,(∑i,x i^k)=a ∧ ∃i,IsUnit (x i) := by
  let x : Fin (l.length+1) → R := Fin.cons 1 l.get
  have hsum : (∑i,x i^k)=a := by
    simp only [x,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,one_pow]
    rw [sum_power_get_eq_localPowerListSum,hl]
    ring
  have hunit : ∃i,IsUnit (x i) := ⟨0,by simpa [x] using (isUnit_one : IsUnit (1:R))⟩
  exact power_tuple_with_unit_mono k hk ⟨x,hsum,hunit⟩ hlen

#print axioms residue_charP_of_prime_not_isUnit
#print axioms unit_power_tuple_of_short_list
end WaringSiegel.WSL4
