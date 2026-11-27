import WaringSiegel.WSL3MomentCompactKernel
import WaringSiegel.WSL3MomentInsertionGrowth

/-! # Fixed compact cutoffs for every archimedean frequency box -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField ContDiff
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem exists_smooth_compact_cutoff (D : ℝ) (hD : 0 < D) :
    ∃ f : mixedSpace K → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      ∀ x, ‖x‖ ≤ D → f x = 1 := by
  let b : ContDiffBump (0 : mixedSpace K) :=
    ⟨D, D+1, hD, by linarith⟩
  refine ⟨fun x => (b x : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp), ?_⟩
  intro x hx
  have hb : b x=1 := b.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  change (b x : ℂ) = 1
  rw [hb, Complex.ofReal_one]

/-- Fully closed shifted-kernel estimate for actual bounded algebraic-integer
frequencies. The smooth cutoff is constructed in the proof, not supplied as a
hypothesis. -/
theorem nonnegative_boxed_polynomial_shifted_minor_bound (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ B H : ℝ, 1 ≤ B → B^2 ≤ H →
      ∀ θ : mixedSpace K, ∀ k : ℕ, 0 < k →
      (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
        traceMajorArcUnion (B*H) ((k:ℝ)^finrank ℚ K * B^finrank ℚ K) →
      ∀ Y : Finset (𝓞 K),
      (∀ y ∈ Y, ∀ v : InfinitePlace K, v (y:K) ≤ B) →
      ∀ {α : Type*} [Fintype α] (δ : α → 𝓞 K) (w : α → ℂ),
      (∀ a, ∀ v : InfinitePlace K, v (δ a:K) ≤ D*H) →
      (∀ β, ‖frequencySum (fun a => integerCoordinates K (δ a)) w β‖ =
        (frequencySum (fun a => integerCoordinates K (δ a)) w β).re) →
      (∑ y : Y, (frequencySum (fun a => integerCoordinates K (δ a)) w
        (archimedeanTorusHom (((k:ℝ) • θ)*mixedEmbedding K (y.val:K)))).re) ≤
      C * H^finrank ℚ K * ∫ β,
        (frequencySum (fun a => integerCoordinates K (δ a)) w β).re ∂latticeHaar := by
  obtain ⟨f, hf, hc, hcut⟩ := exists_smooth_compact_cutoff (K := K) (D+1) (by linarith)
  obtain ⟨C, hC, hb⟩ := nonnegative_polynomial_shifted_minor_bound f hf hc
  refine ⟨C, hC, ?_⟩
  intro B H hB hBH θ k hk hminor Y hY α inst δ w hδ hreal
  apply hb B H hB hBH θ k hk hminor Y hY δ w _ hreal
  intro a
  apply hcut
  apply (mixed_norm_le_iff _ _).mpr
  intro v
  have hH : 0 < H := lt_of_lt_of_le (sq_pos_of_pos (by linarith : 0 < B)) hBH
  rw [normAtPlace_smul, abs_of_pos (inv_pos.mpr hH), normAtPlace_apply]
  calc
    H⁻¹ * v (δ a:K) ≤ H⁻¹ * (D*H) :=
      mul_le_mul_of_nonneg_left (hδ a v) (inv_nonneg.mpr hH.le)
    _ = D := by field_simp
    _ ≤ D+1 := by linarith

#print axioms nonnegative_boxed_polynomial_shifted_minor_bound
end WaringSiegel.WSL3
