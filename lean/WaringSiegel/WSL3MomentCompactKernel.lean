import WaringSiegel.WSL3MomentSlices
import WaringSiegel.WSL3PoissonCompactShifted
import WaringSiegel.WSL3PoissonMixedSupport
import WaringSiegel.WSL3IntegerBoxLower
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Actual compact Poisson kernels acting on moment slices

The finite Fourier reproducing kernel is identified with the actual smooth
lattice sum. Its shifted minor-arc estimate follows from the proved Poisson
bound, uniformly over every nonnegative Fourier polynomial whose frequencies
lie in the region where the fixed cutoff equals one.
-/
noncomputable section
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField ContDiff
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]
variable {α : Type*} [Fintype α]

theorem latticeCharacter_integer_arch (a : 𝓞 K) (β : mixedSpace K) :
    latticeCharacter (integerCoordinates K a) (archimedeanTorusHom β) =
      archimedeanTraceCharacter β (mixedEmbedding K (a:K)) := by
  rw [latticeCharacter_archimedeanTorusHom]
  simp only [archimedeanTraceCharacter, mul_comm β (mixedEmbedding K (a:K))]

theorem compact_kernel_frequencySum (f : mixedSpace K → ℂ) (hc : HasCompactSupport f)
    (H : ℝ) (hH : H ≠ 0) (β : mixedSpace K) :
    frequencySum (fun a : compactIntegerSupport f hc H hH => integerCoordinates K a.val)
      (fun a => f (H⁻¹ • mixedEmbedding K (a.val:K))) (archimedeanTorusHom β) =
        compactLinearSum f H β := by
  simp only [frequencySum, latticeCharacter_integer_arch]
  rw [Finset.sum_coe_sort (compactIntegerSupport f hc H hH)
    (fun a : 𝓞 K => f (H⁻¹ • mixedEmbedding K (a:K)) *
      archimedeanTraceCharacter β (mixedEmbedding K (a:K)))]
  symm
  apply tsum_eq_sum
  intro a ha
  have hz : f (H⁻¹ • mixedEmbedding K (a:K)) = 0 := by
    simpa only [mem_compactIntegerSupport, not_not] using ha
  rw [hz, zero_mul]

theorem compact_kernel_reproducing_coefficient (f : mixedSpace K → ℂ)
    (hc : HasCompactSupport f) (H : ℝ) (hH : H ≠ 0) (a : 𝓞 K)
    (ha : f (H⁻¹ • mixedEmbedding K (a:K)) = 1) :
    (∑ b : compactIntegerSupport f hc H hH,
      if integerCoordinates K a = integerCoordinates K b.val then
        f (H⁻¹ • mixedEmbedding K (b.val:K)) else 0) = 1 := by
  have ham : a ∈ compactIntegerSupport f hc H hH :=
    (mem_compactIntegerSupport _ _ _ _ _).mpr (by rw [ha]; exact one_ne_zero)
  let a0 : compactIntegerSupport f hc H hH := ⟨a, ham⟩
  rw [Finset.sum_eq_single a0]
  · exact (if_pos rfl).trans ha
  · intro b hb hba
    apply if_neg
    intro he
    exact hba (Subtype.ext (integerCoordinates_injective K he).symm)
  · exact fun h => False.elim (h (Finset.mem_univ _))

/-- The kernel estimate has no remaining summability, Fourier, or Poisson
hypothesis. Only the explicit cutoff support condition on the input frequencies
and nonnegativity of the input Fourier polynomial are required. -/
theorem nonnegative_polynomial_shifted_minor_bound (f : mixedSpace K → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 < C ∧ ∀ B H : ℝ, 1 ≤ B → B^2 ≤ H →
      ∀ θ : mixedSpace K, ∀ k : ℕ, 0 < k →
      (Submodule.Quotient.mk θ : ArchimedeanTraceTorus K) ∉
        traceMajorArcUnion (B*H) ((k:ℝ)^finrank ℚ K * B^finrank ℚ K) →
      ∀ Y : Finset (𝓞 K),
      (∀ y ∈ Y, ∀ v : InfinitePlace K, v (y:K) ≤ B) →
      ∀ {α : Type*} [Fintype α] (δ : α → 𝓞 K) (w : α → ℂ),
      (∀ a, f (H⁻¹ • mixedEmbedding K (δ a:K)) = 1) →
      (∀ β, ‖frequencySum (fun a => integerCoordinates K (δ a)) w β‖ =
        (frequencySum (fun a => integerCoordinates K (δ a)) w β).re) →
      (∑ y : Y, (frequencySum (fun a => integerCoordinates K (δ a)) w
        (archimedeanTorusHom (((k:ℝ) • θ)*mixedEmbedding K (y.val:K)))).re) ≤
      C * H^finrank ℚ K * ∫ β,
        (frequencySum (fun a => integerCoordinates K (δ a)) w β).re ∂latticeHaar := by
  obtain ⟨C, hC, hb⟩ := trace_compactLinearSum_shifted_minor_bound f hf hc
  refine ⟨C, hC, ?_⟩
  intro B H hB hBH θ k hk hminor Y hbox α inst δ w hcut hreal
  have hH : 0 < H := lt_of_lt_of_le (sq_pos_of_pos (by linarith : 0 < B)) hBH
  apply frequencySum_shifted_kernel_average_le
    (fun a => integerCoordinates K (δ a)) w
    (fun a : compactIntegerSupport f hc H hH.ne' => integerCoordinates K a.val)
    (fun a => f (H⁻¹ • mixedEmbedding K (a.val:K)))
    (fun a => compact_kernel_reproducing_coefficient f hc H hH.ne' (δ a) (hcut a)) hreal
  intro β
  obtain ⟨η, rfl⟩ := archimedeanTorusHom_surjective β
  have h := hb B H hB hBH θ (-η) k hk hminor Y (by
    intro y hy v
    simpa only [normAtPlace_apply] using hbox y hy v)
  calc
    _ = ∑ y : Y, ‖compactLinearSum f H
        (((k:ℝ) • θ)*mixedEmbedding K (y.val:K)+(-η))‖ := by
      apply Finset.sum_congr rfl
      intro y hy
      congr 1
      rw [← map_sub, compact_kernel_frequencySum]
      rfl
    _ ≤ _ := h

#print axioms nonnegative_polynomial_shifted_minor_bound
end WaringSiegel.WSL3
