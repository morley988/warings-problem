import WaringSiegel.NumberFieldTargets

/-! # Strict positivity of the summands

Deleting zero coordinates converts a bound phrased with totally nonnegative
roots into the version with nonzero, totally positive roots. The number of
summands and the norm bound are retained.
-/
noncomputable section
open scoped NumberField BigOperators Classical
open WaringSiegel

namespace WaringLinear
variable {K : Type*} [Field K] [NumberField K]

def PositiveRepresentation (k s : ℕ) (C : ℝ) (ν : 𝓞 K) : Prop :=
  ∃ t : ℕ, t ≤ s ∧ ∃ x : Fin t → 𝓞 K,
    (∀ i, x i ≠ 0 ∧ TotallyPositive (x i)) ∧
    (∑ i, (x i)^k = ν) ∧
    (∀ i, absNorm (x i) ≤ C*absNorm ν^(1/(k:ℝ)))

theorem positiveRepresentation_iff (k s : ℕ) (hk : k ≠ 0) (C : ℝ) (ν : 𝓞 K) :
    PositiveRepresentation k s C ν ↔ RepresentableByAtMost k s C ν := by
  classical
  constructor
  · rintro ⟨t,ht,x,hpos,hs,hn⟩
    exact ⟨t,ht,x,fun i σ => (hpos i).2 σ |>.le,hs,hn⟩
  · rintro ⟨t,ht,x,hpos,hs,hn⟩
    let S : Finset (Fin t) := Finset.univ.filter (fun i => x i ≠ 0)
    let e := S.equivFin.symm
    refine ⟨S.card, (Finset.card_le_univ S).trans (by simpa using ht),
      fun j => x (e j).1, ?_, ?_, fun j => hn (e j).1⟩
    · intro j
      have hne : x (e j).1 ≠ 0 := (Finset.mem_filter.mp (e j).2).2
      refine ⟨hne, fun σ => lt_of_le_of_ne (hpos _ σ) ?_⟩
      have hK : ((x (e j).1 : 𝓞 K) : K) ≠ 0 := by exact_mod_cast hne
      exact Ne.symm ((map_ne_zero σ).mpr hK)
    · calc
        (∑ j, x (e j).1 ^k) = ∑ i : S, x i.1 ^k := e.sum_comp (fun i : S => x i.1 ^k)
        _ = ∑ i ∈ S, x i^k := Finset.sum_coe_sort S (fun i => x i^k)
        _ = ∑ i, x i^k := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i hi hout
          have hz : x i = 0 := by simpa [S] using hout
          simp [hz,hk]
        _ = ν := hs

#print axioms positiveRepresentation_iff
end WaringLinear
