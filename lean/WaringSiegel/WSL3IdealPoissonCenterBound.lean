import WaringSiegel.WSL3IdealPoissonCubicMajor
import WaringSiegel.WSL3IdealPoissonCenter

/-!
# Actual field-center cubic estimate with the finite Weil gap explicit

The only conditional input is a uniform estimate for the literal complete
cubic sum with arbitrary linear trace twist. Every analytic and arithmetic
identification used to transfer it to the actual smooth source is proved.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 700000
variable {K : Type*} [Field K] [NumberField K]

/-- Actual major-arc cubic estimate. The displayed finite twisted-sum hypothesis
is deliberately retained: the pure cubic Gauss bound does not imply it. -/
theorem smoothCubic_center_major_bound (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (κ : ℝ), 0 ≤ κ →
      (∀ ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
          ((traceConductor γ).absNorm:ℝ)*κ) →
      ∀ (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ((traceConductor γ).absNorm:ℝ)*productArcWeight (P^3) θ ≤ P^(finrank ℚ K) →
      ‖∑' x : 𝓞 K, smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^3)‖ ≤
          C*κ*P^(finrank ℚ K)/cubicProductStationaryWeight (P^3 • θ) := by
  obtain ⟨C,hC,hb⟩ := smoothCubic_residue_major_bound (K:=K) rho R hrho hR
  refine ⟨C,hC,fun γ κ hκ hfinite P hP θ hmaj => ?_⟩
  letI := fieldCenterResidueFintype γ
  have hN : 0 < ((traceConductor γ).absNorm:ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff (traceConductor γ)).mpr inferInstance))
  have h := hb (traceConductor γ) (traceConductor_ne_zero γ)
    (fun q => fieldCenterResidueChar γ (q^3)) (((traceConductor γ).absNorm:ℝ)*κ)
    (mul_nonneg hN.le hκ) (by intro ξ; exact hfinite ξ) P hP θ hmaj
  have hquot : (((traceConductor γ).absNorm:ℝ)*κ)/((traceConductor γ).absNorm:ℝ) = κ := by
    field_simp
  rw [hquot] at h
  have he : (∑' x : 𝓞 K, smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
      archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^3)) =
      ∑' x : 𝓞 K, fieldCenterResidueChar γ ((Ideal.Quotient.mk (traceConductor γ) x)^3)*
        (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3)) := by
    apply tsum_congr
    intro x
    rw [← (Ideal.Quotient.mk (traceConductor γ)).map_pow x 3,
      fieldCenterResidueChar_mk,traceCharacter_frequency_add]
    simp only [map_pow,Complex.real_smul]
    ring
  rw [he]
  exact h

#print axioms smoothCubic_center_major_bound
end WaringSiegel.WSL3Poisson
