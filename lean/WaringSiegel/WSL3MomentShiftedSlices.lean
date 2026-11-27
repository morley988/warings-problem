import WaringSiegel.WSL3MomentSlices
import WaringSiegel.WSL3MomentCommonShift

/-!
# Common translation of literal lower-coefficient slices

The common shift is proved by the finite Fourier expansion, including the
linear Fourier-completion twist. It changes the degree-(k-1) coefficient by
exactly k*z*theta and leaves the lower-equation slice unchanged.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate Classical
namespace WaringSiegel.WSL3
open WSL2
variable {A α ι : Type*} [CommRing A] [Fintype α] [Fintype ι]

theorem vinogradovEquations_iff_powerDifferences (R s : ℕ) (nodes : α → A)
    (x y : Fin s → α) :
    VinogradovEquations R s nodes x y ↔
      ∀ j, j < R+1 → powerSumDifference j s (nodes ∘ x) (nodes ∘ y) = 0 := by
  constructor
  · intro h j hj
    by_cases hj0 : j=0
    · subst j; exact powerSumDifference_zero _ _ _
    · simpa only [powerSumDifference, Function.comp_apply, show j-1+1=j by omega] using
        sub_eq_zero.mpr (h ⟨j-1, by omega⟩)
  · intro h j
    exact sub_eq_zero.mp (h (j.val+1) (by omega))

theorem vinogradovEquations_add_iff (R s : ℕ) (nodes : α → A) (z : A)
    (x y : Fin s → α) :
    VinogradovEquations R s (fun a => nodes a+z) x y ↔
      VinogradovEquations R s nodes x y := by
  rw [vinogradovEquations_iff_powerDifferences, vinogradovEquations_iff_powerDifferences]
  constructor
  · intro h j hj
    have h' := common_shift_preserves_lower_equations (R+1) s
      (fun i => nodes (x i)+z) (fun i => nodes (y i)+z) z h j hj
    simpa only [add_sub_cancel_right, Function.comp_apply] using h'
  · intro h j hj
    have h' := common_shift_preserves_lower_equations (R+1) s
      (nodes ∘ x) (nodes ∘ y) (-z) h j hj
    simpa only [sub_neg_eq_add, Function.comp_apply] using h'

theorem pairedTupleCoefficient_mul (s : ℕ) (w t : α → ℂ)
    (xy : (Fin s → α) × (Fin s → α)) :
    pairedTupleCoefficient s (fun a => w a*t a) xy =
      pairedTupleCoefficient s w xy * pairedTupleCoefficient s t xy := by
  simp only [pairedTupleCoefficient, Finset.prod_mul_distrib, map_mul]
  ring

theorem pairedTupleCoefficient_character (coord : A →+ (ι → ℤ)) (s : ℕ)
    (phase : α → A) (θ : ι → AddCircle (1 : ℝ))
    (xy : (Fin s → α) × (Fin s → α)) :
    pairedTupleCoefficient s (fun a => latticeCharacter (coord (phase a)) θ) xy =
      latticeCharacter (coord ((∑ i, phase (xy.1 i)) - ∑ i, phase (xy.2 i))) θ := by
  simp only [pairedTupleCoefficient, ← WaringSiegel.latticeCharacter_sum,
    ← map_sum, ← latticeCharacter_sub, ← map_sub]

theorem common_shift_top_add_identity (R s : ℕ) (x y : Fin s → A) (z : A)
    (hlow : ∀ j, j < R+1 → powerSumDifference j s x y = 0) :
    powerSumDifference (R+2) s (fun i => x i+z) (fun i => y i+z) =
      powerSumDifference (R+2) s x y + (R+2 : A)*z*powerSumDifference (R+1) s x y := by
  have h := common_shift_top_identity_succ R s x y (-z) hlow
  simpa only [sub_neg_eq_add, mul_neg, neg_mul, Nat.cast_add, Nat.cast_ofNat] using h

/-- Exact shift of a lower-coefficient moment, with arbitrary linear Fourier
completion twist. The k-1 coefficient is the only new surviving coefficient. -/
theorem shifted_lower_moment_eq_slice (coord : A →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (R s : ℕ) (hR : 1 ≤ R) (nodes : α → A)
    (z : A) (θ β γ : ι → AddCircle (1 : ℝ))
    (hγ : ∀ a : A, latticeCharacter (coord a) γ =
      latticeCharacter (coord ((R+2 : A)*z*a)) θ) :
    (∫ η, ‖frequencySum (vinogradovFrequency coord R (fun a => nodes a+z))
      (fun a => latticeCharacter (coord ((nodes a+z)^(R+2))) θ *
        latticeCharacter (coord (nodes a)) β) η‖^(2*s) ∂latticeHaar) =
      sliceMoment s (vinogradovFrequency coord R nodes)
        (fun a => coord (nodes a^(R+1)))
        (fun a => latticeCharacter (coord (nodes a^(R+2))) θ) γ := by
  apply Complex.ofReal_injective
  rw [integral_norm_frequencySum_even_complex]
  unfold sliceMoment
  rw [integral_norm_frequencySum_even_complex]
  apply Finset.sum_congr rfl
  intro xy hxy
  simp only [vinogradov_frequency_eq_iff coord hcoord,
    vinogradovEquations_add_iff]
  by_cases hlow : VinogradovEquations R s nodes xy.1 xy.2
  · rw [if_pos hlow, if_pos hlow]
    rw [pairedTupleCoefficient_mul, pairedTupleCoefficient_mul]
    simp only [pairedTupleCoefficient_character]
    have hlo := (vinogradovEquations_iff_powerDifferences R s nodes xy.1 xy.2).mp hlow
    have hlin : (∑ i, nodes (xy.1 i)) - ∑ i, nodes (xy.2 i) = 0 := by
      simpa only [powerSumDifference, Function.comp_apply, pow_one] using hlo 1 (by omega)
    rw [hlin, map_zero, latticeCharacter_zero, mul_one]
    change latticeCharacter (coord (powerSumDifference (R+2) s
      (fun i => nodes (xy.1 i)+z) (fun i => nodes (xy.2 i)+z))) θ = _
    have htop := common_shift_top_add_identity R s (nodes ∘ xy.1) (nodes ∘ xy.2) z hlo
    dsimp only [Function.comp_def] at htop
    rw [htop, map_add, latticeCharacter_add]
    congr 1
    exact (hγ (powerSumDifference (R+1) s (nodes ∘ xy.1) (nodes ∘ xy.2))).symm
  · rw [if_neg hlow, if_neg hlow]

#print axioms shifted_lower_moment_eq_slice
end WaringSiegel.WSL3
