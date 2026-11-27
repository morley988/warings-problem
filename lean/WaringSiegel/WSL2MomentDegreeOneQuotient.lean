import WaringSiegel.WSL2MomentResidueTransport
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Actual ZMod quotients at an unramified residue-degree-one prime

The local hypotheses are explicit: the prime ideal has norm p and the
valuation of p is one.  From these hypotheses the prime-power quotient
isomorphisms are proved, rather than postulated.  Existence of such a prime
is a separate obligation.
-/

noncomputable section
open scoped NumberField WithZero

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

theorem degreeOne_primePower_quotient_card
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p n : ℕ)
    (hnorm : Ideal.absNorm v.asIdeal=p) :
    Nat.card (𝓞 K ⧸ v.asIdeal^n)=p^n := by
  rw [← Submodule.cardQuot_apply,← Ideal.absNorm_apply,map_pow,hnorm]

theorem degreeOne_primePower_charP
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    (hnorm : Ideal.absNorm v.asIdeal=p)
    (hunramified : v.intValuation (p : 𝓞 K)=WithZero.exp (-1 : ℤ)) (n : ℕ) :
    CharP (𝓞 K ⧸ v.asIdeal^n) (p^n) := by
  let Q := 𝓞 K ⧸ v.asIdeal^n
  have hcard : Nat.card Q=p^n := degreeOne_primePower_quotient_card v p n hnorm
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero n hp.ne_zero)
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fact p.Prime := ⟨hp⟩
  apply charP_of_prime_pow_injective Q p n
  · simpa only [Nat.card_eq_fintype_card] using hcard
  · intro i hi hpi
    have hmem : (p : 𝓞 K)^i∈v.asIdeal^n := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa only [map_pow,map_natCast] using hpi
    have hv := (v.intValuation_le_pow_iff_mem ((p : 𝓞 K)^i) n).mpr hmem
    rw [map_pow,hunramified,← WithZero.exp_nsmul] at hv
    simp only [nsmul_eq_mul,mul_neg,mul_one] at hv
    have hni : (n : ℤ) ≤ (i : ℤ) := by
      have h := WithZero.coe_le_coe.mp hv
      change -(i : ℤ) ≤ -(n : ℤ) at h
      omega
    omega

/-- The quotient equivalence needed by the native integer source transport,
constructed from actual norm and unramified valuation hypotheses. -/
def degreeOne_primePower_quotient_equiv
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    (hnorm : Ideal.absNorm v.asIdeal=p)
    (hunramified : v.intValuation (p : 𝓞 K)=WithZero.exp (-1 : ℤ)) (n : ℕ) :
    (𝓞 K ⧸ v.asIdeal^n) ≃+* ZMod (p^n) := by
  let Q := 𝓞 K ⧸ v.asIdeal^n
  have hcard : Nat.card Q=p^n := degreeOne_primePower_quotient_card v p n hnorm
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero n hp.ne_zero)
  letI : Fintype Q := Fintype.ofFinite Q
  letI : CharP Q (p^n) := degreeOne_primePower_charP v p hp hnorm hunramified n
  exact (ZMod.ringEquiv Q (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm

end WaringSiegel.WSL2
