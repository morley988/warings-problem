import WaringSiegel.WSL4RamanujamCoefficientRing
import WaringSiegel.WSL4RamanujamDigitBudget
import WaringSiegel.WSL4MajorRamanujamHensel

/-! # Actual short power representations of the rational interpolation coefficients

The precision is the proved sharp Ramanujam precision. The result works
in any complete local ring of the indicated residue characteristic,
including every ramified completion occurring in the number-field target.
-/
noncomputable section
open IsLocalRing
namespace WaringSiegel.WSL4Local
open WSL4
variable {R : Type*} [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R]

theorem rationalPrimeCoefficient_power_list
    (p n r : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
    (hn : 0<n) (hnu : IsUnit (n:R)) {a : R}
    (ha : a∈rationalPrimeCoefficientRing p R) :
    ∃l : List R,l.length≤4*(n*p^r)+1 ∧ localPowerListSum (n*p^r) l=a := by
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
  · have hbudget := coefficient_power_list_budget p n r hp.two_le
    simp only [List.length_cons]
    dsimp [ramanujamLiftPrecision,ramanujamLiftOffset] at hlen
    omega
  · rw [localPowerListSum_cons,hy]
    ring

#print axioms rationalPrimeCoefficient_power_list
end WaringSiegel.WSL4Local
