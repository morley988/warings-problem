import WaringSiegel.WSL3MomentSliceKernel

/-! # The shifted slice bound retaining the top phase

The right side is the actual slice integral. It is deliberately retained so
that subsequent integration of the top coefficient imposes the last power-sum
equation. Taking absolute values of its Fourier coefficients too early would
lose that equation.
-/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem monomial_slice_shifted_minor_bound_exact (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ B H : ℝ, 1 ≤ B → B^2 ≤ H →
      ∀ θ : mixedSpace K, ∀ k : ℕ, 0 < k →
      (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
        traceMajorArcUnion (B*H) ((k:ℝ)^finrank ℚ K * B^finrank ℚ K) →
      ∀ Y : Finset (𝓞 K),
      (∀ y ∈ Y, ∀ v : InfinitePlace K, v (y:K) ≤ B) →
      ∀ {α : Type*} [Fintype α] (nodes : α → 𝓞 K) (w : α → ℂ) (R s : ℕ),
      (∀ x y : Fin s → α, ∀ v : InfinitePlace K,
        v (((∑ i, nodes (x i)^(R+1)) - ∑ i, nodes (y i)^(R+1) : 𝓞 K):K) ≤ D*H) →
      (∑ y : Y, sliceMoment s (vinogradovFrequency (integerCoordinates K) R nodes)
        (fun a => integerCoordinates K (nodes a^(R+1))) w
        (archimedeanTorusHom (((k:ℝ) • θ)*mixedEmbedding K (y.val:K)))) ≤
      C * H^finrank ℚ K * ∫ β,
        sliceMoment s (vinogradovFrequency (integerCoordinates K) R nodes)
          (fun a => integerCoordinates K (nodes a^(R+1))) w β ∂latticeHaar := by
  obtain ⟨C, hC, hb⟩ := nonnegative_boxed_polynomial_shifted_minor_bound (K := K) D hD
  refine ⟨C, hC, ?_⟩
  intro B H hB hBH θ k hk hminor Y hY α inst nodes w R s hδ
  let v := vinogradovFrequency (integerCoordinates K) R nodes
  let u : α → NumberFieldCoordinateIndex K → ℤ := fun a => integerCoordinates K (nodes a^(R+1))
  let δ : (Fin s → α) × (Fin s → α) → 𝓞 K :=
    fun xy => (∑ i, nodes (xy.1 i)^(R+1)) - ∑ i, nodes (xy.2 i)^(R+1)
  have he : (fun xy => integerCoordinates K (δ xy)) = sliceFrequency s u := by
    funext xy
    simp only [δ, u, sliceFrequency, map_sub, map_sum]
  have h := hb B H hB hBH θ k hk hminor Y hY δ (sliceCoefficient s v w)
    (fun xy place => hδ xy.1 xy.2 place) (by
      rw [he]
      exact sliceMoment_frequency_norm s v u w)
  simpa only [he, ← sliceMoment_eq_re] using h

#print axioms monomial_slice_shifted_minor_bound_exact
end WaringSiegel.WSL3
