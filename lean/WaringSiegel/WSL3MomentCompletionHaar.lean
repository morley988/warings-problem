import WaringSiegel.WSL3MomentCompletionSum
import WaringSiegel.WSL3MomentSlices

/-!
# Fourier completion inside an actual Haar moment

The interchange of Euclidean completion integration and torus moment
integration is justified by an explicit integrable majorant. No Fubini or
integrability assumption remains at the endpoint.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2
variable {K : Type*} [Field K] [NumberField K]
variable {α ι : Type*} [Fintype α] [Fintype ι]
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

theorem completedFiniteSum_joint_continuous (points : α → mixedSpace K)
    (a : (ι → AddCircle (1 : ℝ)) → α → ℂ) (ha : ∀ x, Continuous (fun η => a η x)) (P : ℝ) :
    Continuous (fun p : (ι → AddCircle (1 : ℝ)) × mixedSpace K =>
      completedFiniteSum points (a p.1) P p.2) := by
  unfold completedFiniteSum
  apply continuous_finset_sum
  intro x hx
  exact ((ha x).comp continuous_fst).mul
    (((archimedeanTraceCharacter_frequency_continuous (points x)).comp
      (continuous_const_smul P⁻¹)).comp continuous_snd)

theorem completedFiniteSum_product_integrable (f : 𝓢(mixedSpace K, ℂ))
    (points : α → mixedSpace K) (a : (ι → AddCircle (1 : ℝ)) → α → ℂ)
    (ha : ∀ x, Continuous (fun η => a η x)) (W : ℝ) (hW : 0 ≤ W)
    (hb : ∀ η x, ‖a η x‖ ≤ W) (P : ℝ) (n : ℕ) :
    Integrable (fun p : (ι → AddCircle (1 : ℝ)) × mixedSpace K =>
      ‖weightCompletionAmplitude f p.2‖ * ‖completedFiniteSum points (a p.1) P p.2‖^n)
      (latticeHaar.prod volume) := by
  let M : ℝ := Fintype.card α * W
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) hW
  have hbound (η : ι → AddCircle (1 : ℝ)) (β : mixedSpace K) :
      ‖completedFiniteSum points (a η) P β‖ ≤ M := by
    apply (completedFiniteSum_norm_le points (a η) P β).trans
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun x hx => hb η x)
  have hi : Integrable (fun p : (ι → AddCircle (1 : ℝ)) × mixedSpace K =>
      M^n * ‖weightCompletionAmplitude f p.2‖) (latticeHaar.prod volume) :=
    (integrable_const (M^n)).mul_prod (weightCompletionAmplitude_integrable f).norm
  apply hi.mono'
  · exact (((weightCompletionAmplitude_continuous f).comp continuous_snd).norm.mul
      ((completedFiniteSum_joint_continuous points a ha P).norm.pow n)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ ‖weightCompletionAmplitude f p.2‖ * M^n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound p.1 p.2) n)
          (norm_nonneg _)
      _ = _ := mul_comm _ _

/-- Exact L1 completion-mass cost for the integrated positive integer moment. -/
theorem finite_sum_shifted_weight_haar_completion (f : 𝓢(mixedSpace K, ℂ))
    (points : α → mixedSpace K) (a : (ι → AddCircle (1 : ℝ)) → α → ℂ)
    (ha : ∀ x, Continuous (fun η => a η x)) (W : ℝ) (hW : 0 ≤ W)
    (hb : ∀ η x, ‖a η x‖ ≤ W) (P : ℝ) (z : mixedSpace K) (n : ℕ) :
    (∫ η, ‖∑ x, a η x * f (P⁻¹ • (points x-z))‖^(n+1) ∂latticeHaar) ≤
      (∫ β, ‖weightCompletionAmplitude f β‖)^n *
        ∫ β, ‖weightCompletionAmplitude f β‖ *
          (∫ η, ‖completedFiniteSum points (a η) P β‖^(n+1) ∂latticeHaar) := by
  have hi := completedFiniteSum_product_integrable f points a ha W hW hb P (n+1)
  have hleft : Integrable (fun η =>
      ‖∑ x, a η x * f (P⁻¹ • (points x-z))‖^(n+1)) latticeHaar := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply Continuous.pow
    apply Continuous.norm
    exact continuous_finset_sum _ (fun x hx => (ha x).mul continuous_const)
  calc
    _ ≤ ∫ η, (∫ β, ‖weightCompletionAmplitude f β‖)^n *
        (∫ β, ‖weightCompletionAmplitude f β‖ *
          ‖completedFiniteSum points (a η) P β‖^(n+1)) ∂latticeHaar := by
      apply integral_mono hleft (hi.integral_prod_left.const_mul _)
      intro η
      exact finite_sum_shifted_weight_moment_completion f points (a η) P z n
    _ = (∫ β, ‖weightCompletionAmplitude f β‖)^n *
        ∫ η, (∫ β, ‖weightCompletionAmplitude f β‖ *
          ‖completedFiniteSum points (a η) P β‖^(n+1)) ∂latticeHaar := integral_const_mul _ _
    _ = _ := by
      congr 1
      rw [integral_integral_swap hi]
      apply integral_congr_ae
      filter_upwards with β
      exact integral_const_mul _ _

#print axioms finite_sum_shifted_weight_haar_completion
end WaringSiegel.WSL3
