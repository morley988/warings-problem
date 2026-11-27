import WaringLinear.MixedSupport
import WaringLinear.PositiveRoots

/-! # Mixed Fourier coefficients and bounded, totally positive representations -/
noncomputable section
open MeasureTheory
open scoped BigOperators NumberField Classical ComplexConjugate
open WaringSiegel WaringSiegel.WSL2
namespace WaringLinear
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
variable {ι α β : Type*} [Fintype ι] [Fintype α] [Fintype β]

local instance : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

/-- Mixed positive- and restricted-root coefficients on the lattice torus. -/
theorem mixed_target_coefficient (A : α → ι → ℤ) (B : β → ι → ℤ)
    (a : α → ℂ) (b : β → ℂ) (r s : ℕ) (target : ι → ℤ) :
    (∫ θ, (frequencySum A a θ)^r*(frequencySum B b θ)^s*
      conj (latticeCharacter target θ) ∂latticeHaar) =
    ∑ p : (Fin r → α) × (Fin s → β),
      if (∑ i, A (p.1 i)) + (∑ j, B (p.2 j)) = target
      then (∏ i, a (p.1 i))*(∏ j, b (p.2 j)) else 0 := by
  simp_rw [frequencySum_pow,frequency_product]
  let V (p : (Fin r → α) × (Fin s → β)) := (∑ i, A (p.1 i))+(∑ j, B (p.2 j))
  let W (p : (Fin r → α) × (Fin s → β)) := (∏ i, a (p.1 i))*(∏ j, b (p.2 j))
  change (∫ θ, frequencySum V W θ * conj (latticeCharacter target θ) ∂latticeHaar) = _
  have h (θ : ι → AddCircle (1:ℝ)) : frequencySum V W θ * conj (latticeCharacter target θ) =
      ∑ p, W p*latticeCharacter (V p-target) θ := by
    simp only [frequencySum,Finset.sum_mul,latticeCharacter_sub,mul_assoc]
  simp_rw [h]
  exact integral_weighted_lattice_sum Finset.univ W V target

/-- A positive major contribution surviving the complementary arcs produces
an actual representation by nested finite supports. The minor premise uses
the integral of the absolute value. -/
theorem mixed_target_if_core_dominates (A : α → ι → ℤ) (B : β → ι → ℤ)
    (a : α → ℂ) (b : β → ℂ) (r s : ℕ) (target : ι → ℤ)
    (M : Set (ι → AddCircle (1:ℝ))) (hM : MeasurableSet M)
    (hcore : (∫ θ in Mᶜ, ‖(frequencySum A a θ)^r*(frequencySum B b θ)^s*
        conj (latticeCharacter target θ)‖ ∂latticeHaar) <
      (∫ θ in M, (frequencySum A a θ)^r*(frequencySum B b θ)^s*
        conj (latticeCharacter target θ) ∂latticeHaar).re) :
    ∃ x : Fin r → α, ∃ y : Fin s → β,
      (∑ i, A (x i))+(∑ j, B (y j))=target := by
  let g (θ : ι → AddCircle (1:ℝ)) :=
    (frequencySum A a θ)^r*(frequencySum B b θ)^s*conj (latticeCharacter target θ)
  have hcont : Continuous g :=
    (((continuous_frequencySum A a).pow _).mul ((continuous_frequencySum B b).pow _)).mul
      (Complex.continuous_conj.comp (continuous_latticeCharacter _))
  have hint := hcont.integrable_of_hasCompactSupport (μ := latticeHaar)
    (HasCompactSupport.of_compactSpace _)
  have hbound : ‖∫ θ in Mᶜ, g θ ∂latticeHaar‖ ≤ ∫ θ in Mᶜ, ‖g θ‖ ∂latticeHaar :=
    norm_integral_le_integral_norm _
  change (∫ θ in Mᶜ, ‖g θ‖ ∂latticeHaar) < (∫ θ in M, g θ ∂latticeHaar).re at hcore
  have hnonzero : (∫ θ, g θ ∂latticeHaar) ≠ 0 := by
    intro hh
    rw [←integral_add_compl hM hint] at hh
    have hneg : (∫ θ in M, g θ ∂latticeHaar) = -(∫ θ in Mᶜ, g θ ∂latticeHaar) :=
      eq_neg_of_add_eq_zero_left hh
    have hb := Complex.re_le_norm (∫ θ in M, g θ ∂latticeHaar)
    rw [hneg,norm_neg] at hb
    rw [hneg] at hcore
    linarith
  unfold g at hnonzero
  rw [mixed_target_coefficient] at hnonzero
  by_contra hnone
  apply hnonzero
  apply Finset.sum_eq_zero
  rintro ⟨x,y⟩ _
  simp [show (∑ i, A (x i))+(∑ j, B (y j))≠target from fun hh => hnone ⟨x,y,hh⟩]

variable {K : Type*} [Field K] [NumberField K]

/-- The positive-root number-field predicate at a target follows directly from
the actual mixed Fourier coefficient on its coordinate torus, with the supplied
box bounds on both kinds of roots. -/
theorem positive_field_target_of_core (k r s : ℕ) (x : α → 𝓞 K) (y : β → 𝓞 K)
    (a : α → ℂ) (b : β → ℂ) (ν : 𝓞 K) (C : ℝ)
    (hx : ∀ i, (x i)≠0 ∧ ∀ σ : K →+* ℝ, 0 < σ (x i : K))
    (hy : ∀ i, (y i)≠0 ∧ ∀ σ : K →+* ℝ, 0 < σ (y i : K))
    (hxb : ∀ i, absNorm (x i) ≤ C*absNorm ν^(1/(k:ℝ)))
    (hyb : ∀ i, absNorm (y i) ≤ C*absNorm ν^(1/(k:ℝ)))
    (M : Set (NumberFieldCoordinateIndex K → AddCircle (1:ℝ))) (hM : MeasurableSet M)
    (hcore : let A := fun i => integerCoordinates K ((x i)^k)
             let B := fun i => integerCoordinates K ((y i)^k)
             let g := fun θ => (frequencySum A a θ)^r*(frequencySum B b θ)^s*
                    conj (latticeCharacter (integerCoordinates K ν) θ)
             (∫ θ in Mᶜ, ‖g θ‖ ∂latticeHaar) < (∫ θ in M, g θ ∂latticeHaar).re) :
    PositiveRepresentation k (r+s) C ν := by
  obtain ⟨u,v,h⟩ := mixed_target_if_core_dominates _ _ a b r s
    (integerCoordinates K ν) M hM hcore
  refine ⟨r+s,le_rfl,Fin.append (fun i => x (u i)) (fun i => y (v i)),?_,?_,?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hx (u j)
    · simpa using hy (v j)
  · apply integerCoordinates_injective K
    rw [Fin.sum_univ_add,map_add,map_sum,map_sum]
    simpa using h
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hxb (u j)
    · simpa using hyb (v j)

#print axioms mixed_target_if_core_dominates
#print axioms positive_field_target_of_core
end WaringLinear
