import WaringSiegel.WSL3MomentBoxedKernel

/-! # The actual Poisson kernel bound applied to Vinogradov moment slices -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]
variable {A α ι : Type*} [CommRing A] [Fintype α] [Fintype ι]

theorem lower_and_next_equations (coord : A →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (R s : ℕ) (nodes : α → A)
    (x y : Fin s → α)
    (hlow : (∑ i, vinogradovFrequency coord R nodes (x i)) =
      ∑ i, vinogradovFrequency coord R nodes (y i))
    (htop : (∑ i, coord (nodes (x i)^(R+1))) = ∑ i, coord (nodes (y i)^(R+1))) :
    VinogradovEquations (R+1) s nodes x y := by
  have hlo := (vinogradov_frequency_eq_iff coord hcoord R s nodes x y).mp hlow
  have hhi : (∑ i, nodes (x i)^(R+1)) = ∑ i, nodes (y i)^(R+1) :=
    hcoord (by simpa only [map_sum] using htop)
  intro j
  by_cases hj : j.val < R
  · exact hlo ⟨j.val, hj⟩
  · have hjR : j.val=R := by omega
    simpa only [hjR] using hhi

theorem monomial_slice_integral_le_energy (coord : A →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (R s : ℕ) (nodes : α → A) (w : α → ℂ) :
    (∫ β, sliceMoment s (vinogradovFrequency coord R nodes)
      (fun a => coord (nodes a^(R+1))) w β ∂latticeHaar) ≤
      weightedVinogradovEnergy (R+1) s nodes (fun a => ‖w a‖) := by
  rw [sliceMoment_integral]
  unfold weightedVinogradovEnergy
  apply Finset.sum_le_sum
  intro xy hxy
  by_cases h : (∑ i, vinogradovFrequency coord R nodes (xy.1 i)) =
      (∑ i, vinogradovFrequency coord R nodes (xy.2 i)) ∧
      (∑ i, coord (nodes (xy.1 i)^(R+1))) = ∑ i, coord (nodes (xy.2 i)^(R+1))
  · rw [if_pos h, if_pos (lower_and_next_equations coord hcoord R s nodes xy.1 xy.2 h.1 h.2)]
    exact (Complex.re_le_norm _).trans_eq (by
      simp only [pairedTupleCoefficient, norm_mul, Complex.norm_conj, norm_prod])
  · rw [if_neg h]
    split_ifs
    · positivity
    · rfl

/-- Every term is an actual lower-coefficient Haar moment, and the upper
bound is an actual weighted monomial solution energy. -/
theorem monomial_slice_shifted_minor_bound (D : ℝ) (hD : 0 ≤ D) :
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
      C * H^finrank ℚ K * weightedVinogradovEnergy (R+1) s nodes (fun a => ‖w a‖) := by
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
  simp_rw [he, ← sliceMoment_eq_re] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left
    (monomial_slice_integral_le_energy (integerCoordinates K)
      (integerCoordinates_injective K) R s nodes w)
  have hH : 0 ≤ H := le_trans (sq_nonneg B) hBH
  positivity

#print axioms monomial_slice_shifted_minor_bound
end WaringSiegel.WSL3
