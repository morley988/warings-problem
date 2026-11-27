import WaringSiegel.WSL4MajorRamanujamRelativeDigits
import WaringSiegel.WSL4MajorRamanujamRelativeUnits

/-! # The actual 4m Waring bound for localized monogenic coefficients -/
noncomputable section
set_option maxHeartbeats 1500000
open IsLocalRing Polynomial
open scoped Classical
namespace WaringSiegel.WSL4
open WSL4Local
variable {B A : Type*} [CommRing B] [CommRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A]
variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p] [Finite (ResidueField A)]

theorem relativePrimeCoefficientRing_power_list_approx
    (f : B →+* A) (hsurj : Function.Surjective ((residue A).comp f))
    (hker : ∀ b : B,residue A (f b)=0 ↔ (p:B) ∣ b)
    (n r t : ℕ) (hn : 0<n)
    (hspan : ∀ a : ResidueField A,
      a∈AddSubgroup.closure (Set.range (fun x : ResidueField A => x^n)))
    {c : A} (hc : c∈relativePrimeCoefficientRing p f) :
    ∃ l : List A,l.length ≤ n*powerDigitBudget p t ∧
      ∃ b : A,c=localPowerListSum (n*p^r) l+(p:A)^t*b := by
  obtain ⟨a,b,hc⟩ := relativePrimeCoefficientRing_approx p t f hc
  obtain ⟨l,hlen,z,hz⟩ := quotient_power_list_mod_prime_power p
    ((residue A).comp f) hsurj hker n r t hn hspan a
  refine ⟨l.map f,by simpa using hlen,b+f z,?_⟩
  have hzA := congrArg f hz
  simp only [map_sub,map_mul,map_pow,map_natCast] at hzA
  rw [map_localPowerListSum] at hzA
  rw [hc]
  linear_combination hzA

theorem relativePrimeCoefficient_power_list
    (f : B →+* A) (hsurj : Function.Surjective ((residue A).comp f))
    (hker : ∀ b : B,residue A (f b)=0 ↔ (p:B) ∣ b)
    (n r : ℕ) (hn : 0<n) (hnu : IsUnit (n:A))
    (hspan : ∀ a : ResidueField A,
      a∈AddSubgroup.closure (Set.range (fun x : ResidueField A => x^n)))
    {a : A} (ha : a∈relativePrimeCoefficientRing p f) :
    ∃ l : List A,l.length ≤ 4*(n*p^r) ∧ localPowerListSum (n*p^r) l=a := by
  have hp : p.Prime := Fact.out
  have has : a-1∈relativePrimeCoefficientRing p f :=
    (relativePrimeCoefficientRing p f).sub_mem ha (relativePrimeCoefficientRing p f).one_mem
  obtain ⟨l,hlen,b,hb⟩ := relativePrimeCoefficientRing_power_list_approx p f hsurj hker
    n r (ramanujamLiftPrecision p r) hn hspan has
  have hdvd : (p:A)^(ramanujamLiftPrecision p r) ∣
      (a-localPowerListSum (n*p^r) l)-(1:A)^(n*p^r) := by
    refine ⟨b,?_⟩
    rw [one_pow]
    linear_combination hb
  obtain ⟨y,hy,-,-⟩ := power_root_of_dvd_sharp p n r hp hnu 1
    (a-localPowerListSum (n*p^r) l) isUnit_one hdvd
  refine ⟨y::l,?_,?_⟩
  · have hbudget := coefficient_power_list_budget_sharp p n r hp.two_le hn
    simp only [List.length_cons]
    dsimp [ramanujamLiftPrecision,ramanujamLiftOffset] at hlen
    omega
  · rw [localPowerListSum_cons,hy]
    ring

/-- The coefficient algebra and its 4m power bound are both constructed inside
an arbitrary complete local ring with the specified full residue-power span. -/
theorem exists_monogenic_coefficient_power_bound
    [Algebra (ZMod p) (ResidueField A)]
    (n r : ℕ) (hn : 0<n) (hnu : IsUnit (n:A))
    (hspan : ∀ a : ResidueField A,
      a∈AddSubgroup.closure (Set.range (fun x : ResidueField A => x^n))) :
    ∃ F : ℤ[X],F.Monic ∧ F.natDegree=Module.finrank (ZMod p) (ResidueField A) ∧
      ∃ f : AdjoinRoot F →+* A,
        Function.Surjective ((residue A).comp f) ∧
        (∀ b : AdjoinRoot F,residue A (f b)=0 ↔ (p:AdjoinRoot F) ∣ b) ∧
        ∀ a : A,a∈relativePrimeCoefficientRing p f →
          ∃ l : List A,l.length ≤ 4*(n*p^r) ∧ localPowerListSum (n*p^r) l=a := by
  obtain ⟨F,hmon,hdeg,f,hs,hk⟩ := exists_monogenic_coefficient_ring (A:=A) p
  refine ⟨F,hmon,hdeg,f,hs,hk,?_⟩
  intro a ha
  exact relativePrimeCoefficient_power_list p f hs hk n r hn hnu hspan ha

#print axioms relativePrimeCoefficientRing_power_list_approx
#print axioms relativePrimeCoefficient_power_list
#print axioms exists_monogenic_coefficient_power_bound
end WaringSiegel.WSL4
