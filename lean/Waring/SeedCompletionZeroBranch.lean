import Waring.DerivativeZeroCount
import Waring.PolicyCompletionEndpointPartition
import Waring.PolicyCompletionGoodBranch

/-!
# The derivative-zero branch on the actual polynomial auxiliary domain

The domain need not be a Cartesian product. Its parameter and center
projections contain every derivative-zero auxiliary argument. The proved
polynomial root count therefore bounds its full mixed energy by the square
of `#parameters * (degree-1)`, times the actual smooth even moment.
-/

noncomputable section
open scoped BigOperators

namespace Waring.SeedCompletionZeroBranch
open AuxiliaryL2Grouping PolicyCompletionHolder PolicyCompletionEndpointPartition
open PolicyCompletionGoodBranch DerivativeZeroCount SmoothMoments

/-- Complete derivative-zero energy bound with the literal polynomial
frequency, original smooth set, and no derivative root estimate assumed. -/
theorem polynomial_zero_energy_le {κ : Type*} [DecidableEq κ]
    (A : Finset (κ × ℤ)) (F : κ → Polynomial ℤ) (d : ℕ)
    (hdeg : ∀ c ∈ A.image Prod.fst, 0 < (F c).natDegree ∧ (F c).natDegree ≤ d)
    (k s : ℕ) (Q R : ℝ) :
    ((collisionPairs (zeroSmoothEndpoints s A Q R (derivativeMagnitude F))
      (tupleFrequency (polynomialValue F) (fun _ n => ((n^k : ℕ) : ℤ)))).card : ℝ) ≤
      (((A.image Prod.fst).card : ℝ)*((d-1 : ℕ) : ℝ))^2 *
        smoothMoment k (2*s) Q R := by
  classical
  let C := A.image Prod.fst
  let Z := A.image Prod.snd
  let B := finiteTuples (smoothNumbers Q R) s
  let U : (Fin s → ℕ) → ℤ := fun u => ∑ i, (((u i)^k : ℕ) : ℤ)
  have hsub : A.filter (fun a => derivativeMagnitude F a=0) ⊆
      derivativeZeroArguments C Z F := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨ha,hzero⟩
    have hz : (F a.1).derivative.eval a.2=0 := by
      simpa only [derivativeMagnitude,Int.natAbs_eq_zero] using hzero
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ ha,Finset.mem_image_of_mem _ ha⟩,hz⟩
  have hdom : zeroSmoothEndpoints s A Q R (derivativeMagnitude F) ⊆
      derivativeZeroArguments C Z F ×ˢ B :=
    Finset.product_subset_product hsub (Finset.Subset.refl _)
  have hc : ((collisionPairs (zeroSmoothEndpoints s A Q R (derivativeMagnitude F))
      (tupleFrequency (polynomialValue F) (fun _ n => ((n^k : ℕ) : ℤ)))).card : ℝ) ≤
      ((collisionPairs (derivativeZeroArguments C Z F ×ˢ B)
        (fun x => (F x.1.1).eval x.1.2 + U x.2)).card : ℝ) := by
    have hfreq : tupleFrequency (polynomialValue F) (fun _ : Fin s => fun n => ((n^k : ℕ) : ℤ)) =
        (fun x : (κ × ℤ) × (Fin s → ℕ) => (F x.1.1).eval x.1.2+U x.2) := rfl
    rw [hfreq]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
      (Finset.product_subset_product hdom hdom))
  have hz := derivativeZero_collisions_le_of_degree C Z F d hdeg B U
  have htuple : ((collisionPairs B U).card : ℝ)=smoothMoment k (2*s) Q R := by
    rw [smoothMoment_even_eq_card]
    rfl
  rw [htuple] at hz
  exact hc.trans hz

#print axioms polynomial_zero_energy_le

end Waring.SeedCompletionZeroBranch
