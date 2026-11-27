import WaringSiegel.WSL3AuxiliaryTruncation
import WaringSiegel.WSL3PoissonMajorFourthProjection

/-! # Actual conductor-center counting and finite major-arc unions -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped NumberField Classical BigOperators ENNReal
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem primitiveIdealCharacter_card_le_norm (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    letI := primitiveIdealCharacterFintype I
    Fintype.card (PrimitiveIdealCharacter I) ≤ Ideal.absNorm I.1 := by
  letI := idealResidueFintype I.1 I.2
  letI := primitiveIdealCharacterFintype I
  have hc : Fintype.card (𝓞 K ⧸ I.1) = Ideal.absNorm I.1 := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply]; rfl
  have h := Fintype.card_le_of_injective (fun ψ : PrimitiveIdealCharacter I => ψ.1) Subtype.val_injective
  simpa only [AddChar.card_eq,hc] using h

theorem rationalTraceCenterCutoff_weight_sum_le (N : ℕ) (κ : Ideal (𝓞 K) → ℝ) :
    (∑ q ∈ rationalTraceCenterCutoff N, κ (rationalTraceCenterConductor q)^4) ≤
      ∑ I ∈ cubicConductorCutoff N, (Ideal.absNorm I.1 : ℝ)*κ I.1^4 := by
  unfold rationalTraceCenterCutoff
  rw [Finset.sum_map]
  have he (c : CubicConductorCharacter K) :
      rationalTraceCenterConductor (cubicConductorCharacterEquivRationalCenter c) = c.1.1 :=
    cubicConductorCharacterToCenter_conductor c
  simp only [Equiv.toEmbedding_apply,he,cubicCharacterConductorCutoff]
  erw [Finset.sum_sigma (cubicConductorCutoff (K := K) N)
    (fun I => @Finset.univ (PrimitiveIdealCharacter I) (primitiveIdealCharacterFintype I))
    (fun x : (I : {I : Ideal (𝓞 K) // I ≠ 0}) × PrimitiveIdealCharacter I => κ x.1.1^4)]
  apply Finset.sum_le_sum
  intro I hI
  letI := primitiveIdealCharacterFintype I
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast primitiveIdealCharacter_card_le_norm I)
    (by positivity)

def boundedTraceCenterToCutoff (N : ℕ) (q : traceRationalCenters K N) :
    rationalTraceCenterCutoff (K := K) N := by
  let r : RationalTraceCenter K := ⟨q.1,traceCenterRepresentative q,(traceCenterRepresentative_spec q).1⟩
  refine ⟨r,(mem_rationalTraceCenterCutoff N r).mpr ?_⟩
  have he : rationalTraceCenterConductor r = traceConductor (traceCenterRepresentative q) := by
    unfold rationalTraceCenterConductor
    change addCharIdealConductor (traceFrequencyAddChar q.1) = _
    rw [← (traceCenterRepresentative_spec q).1,traceFrequencyAddChar_idealConductor]
  rw [he]
  exact (traceCenterRepresentative_spec q).2

def boundedTraceCenterEquivCutoff (N : ℕ) :
    traceRationalCenters K N ≃ rationalTraceCenterCutoff (K := K) N where
  toFun := boundedTraceCenterToCutoff N
  invFun r := ⟨r.1.1,by
    obtain ⟨γ,hγ⟩ := r.1.2
    refine ⟨γ,hγ,?_⟩
    have hc := (mem_rationalTraceCenterCutoff N r.1).mp r.2
    simpa only [rationalTraceCenterConductor,← hγ,traceFrequencyAddChar_idealConductor] using hc⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv r := by apply Subtype.ext; apply Subtype.ext; rfl

theorem traceRationalCenters_weight_sum_le (N : ℕ) (κ : Ideal (𝓞 K) → ℝ) :
    letI := Fintype.ofFinite (traceRationalCenters K N)
    (∑ q : traceRationalCenters K N, κ (traceConductor (traceCenterRepresentative q))^4) ≤
      ∑ I ∈ cubicConductorCutoff N, (Ideal.absNorm I.1 : ℝ)*κ I.1^4 := by
  letI := Fintype.ofFinite (traceRationalCenters K N)
  have he (q : traceRationalCenters K N) :
      rationalTraceCenterConductor (boundedTraceCenterEquivCutoff N q).1 =
        traceConductor (traceCenterRepresentative q) := by
    change addCharIdealConductor (traceFrequencyAddChar q.1) = _
    rw [← (traceCenterRepresentative_spec q).1,traceFrequencyAddChar_idealConductor]
  have hs := (boundedTraceCenterEquivCutoff (K := K) N).bijective.sum_comp
    (fun q => κ (rationalTraceCenterConductor q.1)^4)
  have hh : (∑ q : traceRationalCenters K N, κ (traceConductor (traceCenterRepresentative q))^4) =
      ∑ q ∈ rationalTraceCenterCutoff N, κ (rationalTraceCenterConductor q)^4 := by
    rw [Finset.sum_coe_sort (rationalTraceCenterCutoff N)
      (fun q => κ (rationalTraceCenterConductor q)^4)] at hs
    simpa only [he] using hs
  rw [hh]
  exact rationalTraceCenterCutoff_weight_sum_le N κ

/-- A finite union estimate, with no disjointness requirement. -/
theorem traceHaar_integral_finite_union_le {ι : Type*} [Fintype ι]
    (S : ι → Set (ArchimedeanTraceTorus K)) (hS : ∀ i, MeasurableSet (S i))
    (f : ArchimedeanTraceTorus K → ℝ) (hf : Continuous f) (hfn : ∀ q, 0 ≤ f q) :
    (∫ q in ⋃ i, S i, f q ∂traceHaar) ≤ ∑ i, ∫ q in S i, f q ∂traceHaar := by
  have hi : Integrable f traceHaar := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpoint (q : ArchimedeanTraceTorus K) : (⋃ i, S i).indicator f q ≤ ∑ i, (S i).indicator f q := by
    by_cases hq : q ∈ ⋃ i, S i
    · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
      rw [Set.indicator_of_mem hq]
      calc
        f q = (S i).indicator f q := (Set.indicator_of_mem hi f).symm
        _ ≤ ∑ j, (S j).indicator f q := Finset.single_le_sum
          (fun j _ => Set.indicator_nonneg (fun x _ => hfn x) _) (Finset.mem_univ i)
    · rw [Set.indicator_of_notMem hq]
      exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun x _ => hfn x) _)
  rw [← integral_indicator (MeasurableSet.iUnion hS)]
  calc
    _ ≤ ∫ q, ∑ i, (S i).indicator f q ∂traceHaar := integral_mono
      (hi.indicator (MeasurableSet.iUnion hS))
      (integrable_finset_sum _ (fun i _ => hi.indicator (hS i))) hpoint
    _ = ∑ i, ∫ q, (S i).indicator f q ∂traceHaar :=
      integral_finset_sum _ (fun i _ => hi.indicator (hS i))
    _ = _ := Finset.sum_congr rfl (fun i _ => integral_indicator (hS i))

end WaringSiegel.WSL3Poisson
#print axioms WaringSiegel.WSL3Poisson.traceRationalCenters_weight_sum_le
#print axioms WaringSiegel.WSL3Poisson.traceHaar_integral_finite_union_le
