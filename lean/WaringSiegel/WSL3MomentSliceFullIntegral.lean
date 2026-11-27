import WaringSiegel.WSL3MomentShiftedSlices
import WaringSiegel.WSL3MomentSliceKernel

/-! # Integrating the retained top phase gives the full Vinogradov system -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Classical ComplexConjugate
namespace WaringSiegel.WSL3
open WSL2
variable {A α ι : Type*} [CommRing A] [Fintype α] [Fintype ι]

theorem vinogradovEquations_succ_iff (R s : ℕ) (nodes : α → A) (x y : Fin s → α) :
    VinogradovEquations (R+1) s nodes x y ↔ VinogradovEquations R s nodes x y ∧
      (∑ i, nodes (x i)^(R+1)) = ∑ i, nodes (y i)^(R+1) := by
  constructor
  · intro h
    exact ⟨fun j => h ⟨j.val, by omega⟩, h ⟨R, by omega⟩⟩
  · rintro ⟨hlow, htop⟩ j
    by_cases hj : j.val < R
    · exact hlow ⟨j.val, hj⟩
    · have hjR : j.val=R := by omega
      simpa only [hjR] using htop

def monomialSliceIntegral (coord : A →+ (ι → ℤ)) (R s : ℕ) (nodes : α → A)
    (θ : ι → AddCircle (1 : ℝ)) : ℝ :=
  ∫ β, sliceMoment s (vinogradovFrequency coord R nodes)
    (fun a => coord (nodes a^(R+1)))
    (fun a => latticeCharacter (coord (nodes a^(R+2))) θ) β ∂latticeHaar

theorem monomialSliceIntegral_nonneg (coord : A →+ (ι → ℤ)) (R s : ℕ)
    (nodes : α → A) (θ : ι → AddCircle (1 : ℝ)) :
    0 ≤ monomialSliceIntegral coord R s nodes θ :=
  integral_nonneg (fun β => sliceMoment_nonneg _ _ _ _ _)

theorem monomialSliceIntegral_expansion (coord : A →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (R s : ℕ) (nodes : α → A)
    (θ : ι → AddCircle (1 : ℝ)) :
    monomialSliceIntegral coord R s nodes θ =
      ∑ xy : (Fin s → α) × (Fin s → α),
        if VinogradovEquations (R+1) s nodes xy.1 xy.2 then
          (latticeCharacter (coord ((∑ i, nodes (xy.1 i)^(R+2)) -
            ∑ i, nodes (xy.2 i)^(R+2))) θ).re else 0 := by
  unfold monomialSliceIntegral
  rw [sliceMoment_integral]
  apply Finset.sum_congr rfl
  intro xy hxy
  rw [pairedTupleCoefficient_character]
  simp only [vinogradov_frequency_eq_iff coord hcoord, ← map_sum, hcoord.eq_iff,
    ← vinogradovEquations_succ_iff]

theorem monomialSliceIntegral_continuous (coord : A →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (R s : ℕ) (nodes : α → A) :
    Continuous (monomialSliceIntegral coord R s nodes) := by
  have he := monomialSliceIntegral_expansion coord hcoord R s nodes
  simp_rw [funext he]
  apply continuous_finset_sum
  intro xy hxy
  split_ifs
  · exact Complex.continuous_re.comp (continuous_latticeCharacter _)
  · exact continuous_const

/-- Orthogonality imposes all R+2 equations. This identity is the full-system
input in the localized minor-arc estimate, not just the degree-(R+1) energy. -/
theorem integral_monomialSliceIntegral (coord : A →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (R s : ℕ) (nodes : α → A) :
    (∫ θ, monomialSliceIntegral coord R s nodes θ ∂latticeHaar) =
      (vinogradovCount (R+2) s nodes : ℝ) := by
  simp_rw [monomialSliceIntegral_expansion coord hcoord]
  rw [integral_finset_sum _ (fun xy _ => by
    split_ifs
    · exact (latticeCharacter_integrable _).re
    · exact integrable_zero _ _ _)]
  calc
    _ = ∑ xy : (Fin s → α) × (Fin s → α),
        if VinogradovEquations (R+2) s nodes xy.1 xy.2 then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro xy hxy
      by_cases hlo : VinogradovEquations (R+1) s nodes xy.1 xy.2
      · simp only [if_pos hlo]
        have hre := integral_re (𝕜 := ℂ) (latticeCharacter_integrable
          (coord ((∑ i, nodes (xy.1 i)^(R+2)) - ∑ i, nodes (xy.2 i)^(R+2))))
        simp only [RCLike.re_eq_complex_re] at hre
        rw [hre, latticeCharacter_orthogonality]
        have hz : coord ((∑ i, nodes (xy.1 i)^(R+2)) - ∑ i, nodes (xy.2 i)^(R+2)) = 0 ↔
            (∑ i, nodes (xy.1 i)^(R+2)) = ∑ i, nodes (xy.2 i)^(R+2) := by
          rw [← map_zero coord, hcoord.eq_iff, sub_eq_zero]
        rw [show R+2=(R+1)+1 by omega, vinogradovEquations_succ_iff]
        simp only [hlo, true_and, apply_ite Complex.re, Complex.one_re, Complex.zero_re, hz]
      · have hfull : ¬ VinogradovEquations (R+2) s nodes xy.1 xy.2 := by
          intro h
          exact hlo ((vinogradovEquations_succ_iff (R+1) s nodes xy.1 xy.2).mp h).1
        simp only [if_neg hlo, if_neg hfull, integral_zero]
    _ = _ := by simp [vinogradovCount, Finset.sum_boole]

#print axioms integral_monomialSliceIntegral
end WaringSiegel.WSL3
