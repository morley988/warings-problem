import Waring.External.GafniTao.WooleySourceCriticalBase
import Waring.External.GafniTao.WooleySourceToPadic
import Waring.External.GafniTao.WooleyPadicToCritical

/-!
Critical VMVT endpoint assembled from S. McColm's MIT-0 native Wooley proof,
pinned at bed45b21cb18f26f4d234422ebaa8b17e6624f05, ported to Lean4.24.
The complete dependency closure replays under the pinned compiler. The final
critical endpoints use only propext, Classical.choice and Quot.sound.
-/
open Finset
open scoped BigOperators
namespace Waring.CriticalVMVT
open GafniTao
noncomputable section

theorem critical_endpoint : VinogradovCriticalEndpointTheorem :=
  vinogradovCriticalEndpoint_of_wooleyPadic
    (wooleyMonomialPadicConcentration_of_polynomialCorollary32
      wooleyPolynomialCorollary32_native)

theorem critical_count_bound {k : ℕ} (hk : 1 ≤ k)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q →
      (fordVinogradovMomentNat (fordVinogradovKappa k) k Q : ℝ) ≤
        C * (Q : ℝ) ^ ((fordVinogradovKappa k : ℕ) + epsilon) := by
  obtain ⟨C, hC, h⟩ := critical_endpoint k epsilon hk hepsilon
  refine ⟨C, hC, fun Q hQ => ?_⟩
  simpa only [fordLambda34_critical] using h Q hQ

theorem degree8 {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q →
      (fordVinogradovMomentNat 36 8 Q : ℝ) ≤
        C * (Q : ℝ) ^ ((36 : ℝ) + epsilon) := by
  simpa [fordVinogradovKappa] using critical_count_bound
    (k := 8) (by norm_num) hepsilon

theorem degree9 {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q →
      (fordVinogradovMomentNat 45 9 Q : ℝ) ≤
        C * (Q : ℝ) ^ ((45 : ℝ) + epsilon) := by
  simpa [fordVinogradovKappa] using critical_count_bound
    (k := 9) (by norm_num) hepsilon

/-- The exact literal tuple-pair equations, displaying every degree1..k. -/
theorem count_eq_literal (s k Q : ℕ) :
    fordVinogradovMomentNat s k Q =
      ((Finset.univ : Finset ((Fin s → Fin Q) × (Fin s → Fin Q))).filter
        (fun xy => ∀ j : Fin k,
          (∑ i : Fin s, ((xy.1 i : ℕ) + 1 : ℤ) ^ ((j : ℕ) + 1)) =
          (∑ i : Fin s, ((xy.2 i : ℕ) + 1 : ℤ) ^ ((j : ℕ) + 1)))).card := by
  simp [fordVinogradovMomentNat, fordVinogradovShiftedCountNat,
    fordRepresentationCount, fordVinogradovPowerVector,
    sub_eq_zero, funext_iff, Finset.univ_product_univ]

/-- A statement containing only literal finite tuples and integer equations. -/
theorem critical_literal_bound {k : ℕ} (hk : 1 ≤ k)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q →
      ((((Finset.univ : Finset
          ((Fin (k * (k + 1) / 2) → Fin Q) ×
           (Fin (k * (k + 1) / 2) → Fin Q))).filter
        (fun xy => ∀ j : Fin k,
          (∑ i : Fin (k * (k + 1) / 2),
            ((xy.1 i : ℕ) + 1 : ℤ) ^ ((j : ℕ) + 1)) =
          (∑ i : Fin (k * (k + 1) / 2),
            ((xy.2 i : ℕ) + 1 : ℤ) ^ ((j : ℕ) + 1)))).card : ℕ) : ℝ) ≤
        C * (Q : ℝ) ^ (((k * (k + 1) / 2 : ℕ) : ℝ) + epsilon) := by
  obtain ⟨C, hC, h⟩ := critical_count_bound hk hepsilon
  refine ⟨C, hC, fun Q hQ => ?_⟩
  simpa only [count_eq_literal, fordVinogradovKappa]
    using h Q hQ

#print axioms critical_endpoint
#print axioms critical_count_bound
#print axioms degree8
#print axioms degree9
#print axioms count_eq_literal
#print axioms critical_literal_bound

end
end Waring.CriticalVMVT
