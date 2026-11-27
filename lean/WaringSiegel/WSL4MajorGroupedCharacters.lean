import WaringSiegel.WSL4MajorSeriesAssembly

/-! # Finite major-arc coefficients grouped by their literal conductor ideals

The regrouping here is finite. In particular it makes no assertion that an
individual-character infinite sum can be regrouped without absolute convergence.
-/
noncomputable section
set_option maxHeartbeats 1200000
open WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

local instance groupedPrimitiveFintype (I : {I : Ideal (𝓞 K) // I≠0}) :
    Fintype (PrimitiveIdealCharacter I) := primitiveIdealCharacterFintype I

def conductorCharactersUpTo (N : ℕ) : Finset (PowerConductorCharacter K) :=
  (cubicConductorCutoff N).sigma (fun _ => Finset.univ)

theorem mem_conductorCharactersUpTo (N : ℕ) (c : PowerConductorCharacter K) :
    c∈conductorCharactersUpTo N ↔ c.1.1.absNorm≤N := by
  rcases c with ⟨I,ψ⟩
  change (Sigma.mk I ψ ∈ (cubicConductorCutoff N).sigma
    (fun J => (Finset.univ : Finset (PrimitiveIdealCharacter J)))) ↔ _
  simpa only [Finset.mem_univ,and_true,mem_cubicConductorCutoff] using
    (Finset.mem_sigma (s := cubicConductorCutoff (K := K) N)
      (t := fun J => (Finset.univ : Finset (PrimitiveIdealCharacter J))) (a := Sigma.mk I ψ))

theorem conductorCharactersUpTo_map (N : ℕ) :
    (conductorCharactersUpTo (K := K) N).map
      cubicConductorCharacterEquivRationalCenter.toEmbedding = rationalCentersUpTo N := by
  ext q
  rw [Finset.mem_map]
  constructor
  · rintro ⟨c,hc,rfl⟩
    rw [mem_rationalCentersUpTo]
    change (rationalTraceCenterConductor (cubicConductorCharacterToCenter c)).absNorm≤N
    rw [cubicConductorCharacterToCenter_conductor]
    exact (mem_conductorCharactersUpTo N c).mp hc
  · intro hq
    let c := cubicConductorCharacterEquivRationalCenter.symm q
    refine ⟨c,?_,Equiv.apply_symm_apply _ _⟩
    rw [mem_conductorCharactersUpTo]
    have he := cubicConductorCharacterToCenter_conductor c
    change rationalTraceCenterConductor
      (cubicConductorCharacterEquivRationalCenter c)=c.1.1 at he
    rw [show cubicConductorCharacterEquivRationalCenter c=q from
      Equiv.apply_symm_apply _ _] at he
    rw [← he]
    exact (mem_rationalCentersUpTo N q).mp hq

theorem rationalPower_finite_grouping (k n N : ℕ) (target : 𝓞 K)
    (F : Ideal (𝓞 K) → ℂ) :
    (∑ q∈rationalCentersUpTo N,rationalCenterPowerContribution k n q target *
      F (rationalTraceCenterConductor q)) =
    ∑ I∈cubicConductorCutoff N,idealPrimitivePowerCoefficient k n I.1 I.2 target * F I.1 := by
  rw [← conductorCharactersUpTo_map,Finset.sum_map]
  have he (c : PowerConductorCharacter K) :
      rationalTraceCenterConductor (cubicConductorCharacterEquivRationalCenter c)=c.1.1 :=
    cubicConductorCharacterToCenter_conductor c
  simp only [Equiv.toEmbedding_apply,rationalCenterPowerContribution,Equiv.symm_apply_apply,he]
  unfold conductorCharactersUpTo
  change (∑ c∈(cubicConductorCutoff N).sigma (fun I =>
    (Finset.univ : Finset (PrimitiveIdealCharacter I))),
    powerCharacterContribution k n ⟨c.1,c.2⟩ target * F c.1.1)=_
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro I hI
  change (∑ ψ : PrimitiveIdealCharacter I,powerCharacterContribution k n ⟨I,ψ⟩ target * F I.1)=_
  rw [← Finset.sum_mul]
  congr 1
  simpa only [tsum_fintype] using powerCharacterContribution_fiber_sum k n I target

def idealProductMajorSeries (k n : ℕ) (ρ R L : ℝ) (target : 𝓞 K)
    (b : NumberField.mixedEmbedding.mixedSpace K) : ℂ :=
  ∑ I∈cubicConductorCutoff ⌊L⌋₊,idealPrimitivePowerCoefficient k n I.1 I.2 target *
    productSingularIntegral k n ρ R (L/(I.1.absNorm:ℝ)) b

theorem productMajorSeries_eq_ideal (k n : ℕ) (ρ R L : ℝ) (target : 𝓞 K)
    (b : NumberField.mixedEmbedding.mixedSpace K) :
    productMajorSeries k n ρ R L target b = idealProductMajorSeries k n ρ R L target b :=
  rationalPower_finite_grouping k n ⌊L⌋₊ target
    (fun I => productSingularIntegral k n ρ R (L/(I.absNorm:ℝ)) b)

#print axioms rationalPower_finite_grouping
#print axioms productMajorSeries_eq_ideal
end WaringSiegel.WSL4
