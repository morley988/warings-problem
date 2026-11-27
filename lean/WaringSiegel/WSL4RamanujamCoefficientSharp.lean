import WaringSiegel.WSL4RamanujamCoefficients

/-! # A sharpened 4m budget, including the deliberately inserted unit -/
noncomputable section
open IsLocalRing
namespace WaringSiegel.WSL4Local
open WSL4

theorem powerDigitBudget_sharp_precision_add_one (p r : ℕ) (hp : 2≤p) :
    powerDigitBudget p (r+if p=2 then 2 else 1)+1≤4*p^r := by
  by_cases hp2 : p=2
  · subst p
    simp only [ite_true]
    have h := powerDigitBudget_two (r+2)
    rw [pow_add] at h
    norm_num at h
    omega
  · simp only [if_neg hp2]
    have h := powerDigitBudget_le_twice p r hp
    omega

theorem coefficient_power_list_budget_sharp (p n r : ℕ) (hp : 2≤p) (hn : 0<n) :
    n*powerDigitBudget p (r+if p=2 then 2 else 1)+1≤4*(n*p^r) := by
  have h := Nat.mul_le_mul_left n (powerDigitBudget_sharp_precision_add_one p r hp)
  nlinarith

theorem rationalPrimeCoefficient_power_list_sharp
    {R : Type*} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (p n r : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hn : 0<n) (hnu : IsUnit (n:R)) {a : R}
    (ha : a∈rationalPrimeCoefficientRing p R) :
    ∃l : List R,l.length≤4*(n*p^r) ∧ localPowerListSum (n*p^r) l=a := by
  have hp : p.Prime := Fact.out
  have has : a-1∈rationalPrimeCoefficientRing p R :=
    (rationalPrimeCoefficientRing p R).sub_mem ha (rationalPrimeCoefficientRing p R).one_mem
  obtain ⟨l,hlen,b,hb⟩ := rationalPrimeCoefficientRing_power_list_approx
    p n r (ramanujamLiftPrecision p r) hn has
  have hdvd : (p:R)^(ramanujamLiftPrecision p r)∣
      (a-localPowerListSum (n*p^r) l)-(1:R)^(n*p^r) := by
    refine ⟨b,?_⟩
    rw [one_pow]
    linear_combination hb
  obtain ⟨y,hy,_,_⟩ := power_root_of_dvd_sharp p n r hp hnu 1
    (a-localPowerListSum (n*p^r) l) isUnit_one hdvd
  refine ⟨y::l,?_,?_⟩
  · have hbudget := coefficient_power_list_budget_sharp p n r hp.two_le hn
    simp only [List.length_cons]
    dsimp [ramanujamLiftPrecision,ramanujamLiftOffset] at hlen
    omega
  · rw [localPowerListSum_cons,hy]
    ring

#print axioms rationalPrimeCoefficient_power_list_sharp
end WaringSiegel.WSL4Local
