import WaringSiegel.WSL4MajorSeriesAssembly

/-! # Quantified narrow-arc approximation for the actual Waring coefficient

Every analytic ingredient is supplied by checked source theorems. The
weighted absolute conductor moment remains a visible arithmetic input.
-/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory NumberField NumberField.mixedEmbedding Module WaringSiegel.WSL2 WaringSiegel.WSL3
  WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def cutoffSmoothCoefficient (k n : ℕ) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (L : ℝ)
    (target : 𝓞 K) (htarget : target≠0) : ℂ :=
  ∫ q in traceMajorArcUnion ((rootScale k target)^k) L,
    smoothTraceIntegrand k n ρ R hρ hR (rootScale k target)
      (rootScale_pos htarget k).ne' target q ∂traceHaar

theorem majorScale_pos (k n : ℕ) (P : ℝ) (hP : 0<P) : 0<majorScale (K := K) k n P :=
  Real.rpow_pos_of_pos (pow_pos hP _) _

theorem narrowSmoothCoefficient_full_main_error
    (k s : ℕ) (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (δ : ℝ) (hδ : 0≤δ) (N : ℕ) :
    ∃ C₁ C₂ : ℝ, 0<C₁ ∧ 0<C₂ ∧
      ∀ (target : 𝓞 K) (htarget : target≠0) (M : ℝ),
      Summable (fun q : RationalTraceCenter K =>
        ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
          ‖rationalCenterPowerContribution k (s+1) q target‖) →
      (∑' q : RationalTraceCenter K,((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖rationalCenterPowerContribution k (s+1) q target‖)≤M →
      ∀ L : ℝ, 1≤L → L≤(rootScale k target)^(finrank ℚ K) →
      (2:ℝ)^(finrank ℚ K)*L^2 < (FractionalIdeal.absNorm (inverseDifferent K):ℝ)*
        ((rootScale k target)^k)^(finrank ℚ K) →
        ‖cutoffSmoothCoefficient k (s+1) ρ R hρ hR L target htarget-
          (majorScale (K := K) k (s+1) (rootScale k target):ℂ) *
            (powerSingularSeries k (s+1) target *
            pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
              (smoothRootWeight ρ R) (normalizedTarget k 1 target))‖ ≤
          C₁*(rootScale k target)^(finrank ℚ K*(s+1))*
            (L/(rootScale k target)^(finrank ℚ K))^N*
              (1+L/(rootScale k target)^(finrank ℚ K)) +
          majorScale (K := K) k (s+1) (rootScale k target)*C₂*M/L^δ := by
  obtain ⟨D₁,hD₁,hreplacement⟩ := smoothMajor_poisson_replacement (K := K) k s ρ R hρ hR N
  obtain ⟨C₂,hC₂,hseries⟩ := productMajorSeries_full_truncation_error (K := K) k s hk ρ R hρ hR δ hδ
  refine ⟨D₁,C₂,hD₁,hC₂,?_⟩
  intro target htarget M hs hb L hL hLP hsmall
  have hP := rootScale_pos htarget k
  have hscale := majorScale_pos (K := K) k (s+1) _ hP
  have h1 := hreplacement (rootScale k target) hP L (le_trans zero_le_one hL) hLP hsmall target
  have h2 := hseries target M hs hb L hL (normalizedTarget k 1 target)
  let A := cutoffSmoothCoefficient k (s+1) ρ R hρ hR L target htarget
  let B := smoothMajorMainIntegral k (s+1) ρ R (rootScale k target) L target
  let S := productMajorSeries k (s+1) ρ R L target (normalizedTarget k 1 target)
  let T := powerSingularSeries k (s+1) target *
    pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
      (smoothRootWeight ρ R) (normalizedTarget k 1 target)
  let z : ℝ := majorScale (K := K) k (s+1) (rootScale k target)
  have hB : B=(z:ℂ)*S := smoothMajorMainIntegral_eq_productMajorSeries k (s+1) hk ρ R L target htarget
  have he : A-(z:ℂ)*T=(A-B)+(z:ℂ)*(S-T) := by rw [hB]; ring
  change ‖A-(z:ℂ)*T‖≤_
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add h1
  rw [norm_mul]
  have hz : ‖(z:ℂ)‖=z := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hscale]
  rw [hz]
  exact (mul_le_mul_of_nonneg_left h2 hscale.le).trans_eq (by ring)

#print axioms narrowSmoothCoefficient_full_main_error
end WaringSiegel.WSL4
