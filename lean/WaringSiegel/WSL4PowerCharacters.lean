import WaringSiegel.WSL3CubicRationalSeries

/-! # Literal conductor-character coefficients for arbitrary power sums

The existing exact-conductor character type and rational-center equivalence
are independent of degree. Here their coefficients are given the actual
degree and number of variables. No convergence or positivity is asserted
by defining the series.
-/
noncomputable section
open scoped BigOperators Classical NumberField
namespace WaringSiegel.WSL4Local
variable {K : Type*} [Field K] [NumberField K]

abbrev PowerConductorCharacter (K : Type*) [Field K] [NumberField K] :=
  CubicConductorCharacter K

def powerCharacterContribution (k s : ℕ) (c : PowerConductorCharacter K)
    (ν : 𝓞 K) : ℂ :=
  letI := idealResidueFintype c.1.1 c.1.2
  finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk c.1.1 ν) c.2.1

def idealPrimitivePowerCoefficient (k s : ℕ) (I : Ideal (𝓞 K))
    (hI : I≠0) (ν : 𝓞 K) : ℂ :=
  letI := idealResidueFintype I hI
  ∑ ψ∈primitiveConductorCharacters I,
    finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk I ν) ψ

def rationalCenterPowerContribution (k s : ℕ) (q : RationalTraceCenter K)
    (ν : 𝓞 K) : ℂ :=
  powerCharacterContribution k s (cubicConductorCharacterEquivRationalCenter.symm q) ν

def powerSingularSeries (k s : ℕ) (ν : 𝓞 K) : ℂ :=
  ∑' c : PowerConductorCharacter K,powerCharacterContribution k s c ν

theorem powerCharacterContribution_norm_target_independent (k s : ℕ)
    (c : PowerConductorCharacter K) (ν μ : 𝓞 K) :
    ‖powerCharacterContribution k s c ν‖=‖powerCharacterContribution k s c μ‖ := by
  letI := idealResidueFintype c.1.1 c.1.2
  simp only [powerCharacterContribution,finiteRingPowerCharacterTerm,norm_mul,
    c.2.1.norm_apply,mul_one]

theorem powerCharacterContribution_fiber_sum (k s : ℕ)
    (I : {I : Ideal (𝓞 K) // I≠0}) (ν : 𝓞 K) :
    (∑' ψ : PrimitiveIdealCharacter I,powerCharacterContribution k s ⟨I,ψ⟩ ν)=
      idealPrimitivePowerCoefficient k s I.1 I.2 ν := by
  letI := idealResidueFintype I.1 I.2
  letI := primitiveIdealCharacterFintype I
  simp only [tsum_fintype,powerCharacterContribution,idealPrimitivePowerCoefficient,
    PrimitiveIdealCharacter,primitiveConductorCharacters]
  exact (Finset.sum_subtype (p:=fun ψ => quotientCharacterConductor I.1 ψ=I.1)
    (Finset.univ.filter (fun ψ => quotientCharacterConductor I.1 ψ=I.1))
    (by intro ψ; simp only [Finset.mem_filter,Finset.mem_univ,true_and])
    (fun ψ => finiteRingPowerCharacterTerm k s (Ideal.Quotient.mk I.1 ν) ψ)).symm

theorem rationalCenterPowerContribution_formula (k s : ℕ)
    (q : RationalTraceCenter K) (ν : 𝓞 K) :
    letI := idealResidueFintype (rationalTraceCenterConductor q)
      (rationalTraceCenterConductor_ne_zero q)
    rationalCenterPowerContribution k s q ν =
      ((∑ x : 𝓞 K ⧸ rationalTraceCenterConductor q,
        rationalTraceCenterQuotientCharacter q (x^k)) /
          (Ideal.absNorm (rationalTraceCenterConductor q):ℂ))^s *
        traceTorusCharacter (-ν) q.1 := by
  letI := idealResidueFintype (rationalTraceCenterConductor q)
    (rationalTraceCenterConductor_ne_zero q)
  have hc : Fintype.card (𝓞 K ⧸ rationalTraceCenterConductor q)=
      Ideal.absNorm (rationalTraceCenterConductor q) := by
    rw [← Nat.card_eq_fintype_card,Ideal.absNorm_apply]
    rfl
  unfold rationalCenterPowerContribution
  rw [← rationalTraceCenterPrimitiveIndex_eq_inverse]
  change finiteRingPowerCharacterTerm k s
    (Ideal.Quotient.mk (rationalTraceCenterConductor q) ν)
      (rationalTraceCenterQuotientCharacter q)=_
  unfold finiteRingPowerCharacterTerm finiteRingPowerSum
  rw [hc,← (Ideal.Quotient.mk (rationalTraceCenterConductor q)).map_neg ν]
  rfl

theorem idealPrimitivePowerCoefficient_mul (k s : ℕ)
    (I J : Ideal (𝓞 K)) (hI : I≠0) (hJ : J≠0)
    (h : IsCoprime I J) (ν : 𝓞 K) :
    idealPrimitivePowerCoefficient k s (I*J) (mul_ne_zero hI hJ) ν=
      idealPrimitivePowerCoefficient k s I hI ν *
        idealPrimitivePowerCoefficient k s J hJ ν := by
  letI := idealResidueFintype I hI
  letI := idealResidueFintype J hJ
  letI := idealResidueFintype (I*J) (mul_ne_zero hI hJ)
  exact primitiveConductorCharacterSum_mul I J h k s ν

#print axioms rationalCenterPowerContribution_formula
#print axioms idealPrimitivePowerCoefficient_mul
end WaringSiegel.WSL4Local
