import WaringSiegel.WSL4MajorRamanujamHenselTuple
import Mathlib.Data.Nat.Choose.Factorization

/-! # The exact prime-unit factor in the prime-power binomial coefficient -/
noncomputable section
open IsLocalRing
namespace WaringSiegel.WSL4

theorem prime_power_choose_unit_factor (p r k : ℕ) (hp : p.Prime) (hkr : k ≤ r) :
    ∃ u : ℕ,(p^r).choose (p^k)=p^(r-k)*u ∧ ¬p ∣ u := by
  have hle : p^k ≤ p^r := pow_le_pow_right' hp.one_lt.le hkr
  have hval : ((p^r).choose (p^k)).factorization p=r-k := by
    rw [Nat.factorization_choose_prime_pow hp hle (pow_ne_zero _ hp.ne_zero),
      Nat.factorization_pow_self hp]
  refine ⟨(p^r).choose (p^k)/p^(r-k),?_,?_⟩
  · have he := Nat.ordProj_mul_ordCompl_eq_self ((p^r).choose (p^k)) p
    simpa only [hval] using he.symm
  · have he := Nat.not_dvd_ordCompl hp (Nat.choose_pos hle).ne'
    simpa only [hval] using he

theorem prime_power_choose_unit_factor_pos (p r k : ℕ) (hp : p.Prime) (hkr : k ≤ r) :
    ∃ u : ℕ,0<u ∧ (p^r).choose (p^k)=p^(r-k)*u ∧ ¬p ∣ u := by
  obtain ⟨u,he,hu⟩ := prime_power_choose_unit_factor p r k hp hkr
  refine ⟨u,Nat.pos_of_ne_zero ?_,he,hu⟩
  intro heq
  exact hu (heq ▸ dvd_zero p)

theorem prime_power_choose_local_unit
    {A : Type*} [CommRing A] [IsLocalRing A]
    (p r k : ℕ) (hp : p.Prime) (hkr : k ≤ r)
    [CharP (ResidueField A) p] :
    ∃ u : ℕ,(p^r).choose (p^k)=p^(r-k)*u ∧ IsUnit (u:A) ∧ ¬p ∣ u := by
  obtain ⟨u,he,hu⟩ := prime_power_choose_unit_factor p r k hp hkr
  refine ⟨u,he,?_,hu⟩
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [map_natCast]
  exact fun h => hu ((CharP.cast_eq_zero_iff (ResidueField A) p u).mp h)

#print axioms prime_power_choose_unit_factor
#print axioms prime_power_choose_local_unit
end WaringSiegel.WSL4
