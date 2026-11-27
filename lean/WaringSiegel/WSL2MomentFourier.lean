import WaringSiegel.WeylProducts
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic

/-!
# Actual Haar moments of finite lattice-frequency sums

This module proves weighted moment identities from the actual characters and
probability Haar measure already used for algebraic-integer Weyl sums. No
orthogonality or mean-value estimate is introduced as a hypothesis.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NumberField

namespace WaringSiegel.WSL2

variable {ι : Type*} [Fintype ι]

local instance onePeriodPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance latticeHaarProbability : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

/-- An actual finite sum of lattice characters with complex weights. -/
def frequencySum {α : Type*} [Fintype α] (v : α → ι → ℤ) (w : α → ℂ)
    (θ : ι → AddCircle (1 : ℝ)) : ℂ :=
  ∑ a, w a * latticeCharacter (v a) θ

theorem latticeCharacter_neg (m : ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    latticeCharacter (-m) θ = conj (latticeCharacter m θ) := by
  simp only [latticeCharacter, Pi.neg_apply, fourier_neg, map_prod]

theorem latticeCharacter_sub (m n : ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    latticeCharacter (m - n) θ = latticeCharacter m θ * conj (latticeCharacter n θ) := by
  rw [sub_eq_add_neg, WaringSiegel.latticeCharacter_add, latticeCharacter_neg]

theorem continuous_latticeCharacter (m : ι → ℤ) : Continuous (latticeCharacter m) := by
  unfold latticeCharacter
  exact continuous_finset_prod _ (fun i _ => (fourier (m i)).continuous.comp (continuous_apply i))

theorem continuous_frequencySum {α : Type*} [Fintype α]
    (v : α → ι → ℤ) (w : α → ℂ) : Continuous (frequencySum v w) := by
  unfold frequencySum
  exact continuous_finset_sum _ (fun a _ => continuous_const.mul (continuous_latticeCharacter _))

theorem frequencySum_mul_conj_expansion {α β : Type*} [Fintype α] [Fintype β]
    (v : α → ι → ℤ) (u : β → ι → ℤ) (w : α → ℂ) (z : β → ℂ)
    (θ : ι → AddCircle (1 : ℝ)) :
    frequencySum v w θ * conj (frequencySum u z θ) =
      ∑ p : α × β, (w p.1 * conj (z p.2)) * latticeCharacter (v p.1 - u p.2) θ := by
  classical
  simp only [frequencySum, map_sum, map_mul, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum, latticeCharacter_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Exact weighted cross-correlation, proved by Haar orthogonality. -/
theorem integral_frequencySum_mul_conj {α β : Type*} [Fintype α] [Fintype β]
    (v : α → ι → ℤ) (u : β → ι → ℤ) (w : α → ℂ) (z : β → ℂ) :
    (∫ θ, frequencySum v w θ * conj (frequencySum u z θ) ∂latticeHaar) =
      ∑ p : α × β, if v p.1 = u p.2 then w p.1 * conj (z p.2) else 0 := by
  classical
  simp_rw [frequencySum_mul_conj_expansion]
  have h := integral_weighted_lattice_sum (Finset.univ : Finset (α × β))
    (fun p => w p.1 * conj (z p.2)) (fun p => v p.1 - u p.2) 0
  simpa only [sub_zero, sub_eq_zero] using h

/-- A literal real-valued second moment equals the corresponding weighted energy. -/
theorem integral_norm_frequencySum_sq {α : Type*} [Fintype α]
    (v : α → ι → ℤ) (w : α → ℂ) :
    (∫ θ, ‖frequencySum v w θ‖ ^ 2 ∂latticeHaar) =
      ∑ p : α × α, if v p.1 = v p.2 then (w p.1 * conj (w p.2)).re else 0 := by
  classical
  calc
    (∫ θ, ‖frequencySum v w θ‖ ^ 2 ∂latticeHaar) =
        (∫ θ, frequencySum v w θ * conj (frequencySum v w θ) ∂latticeHaar).re := by
      simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
      rw [integral_complex_ofReal]
      rfl
    _ = _ := by
      rw [integral_frequencySum_mul_conj]
      simp only [Complex.re_sum, apply_ite, Complex.zero_re]

/-- All finite weighted moment integrands are integrable for the actual Haar measure. -/
theorem integrable_norm_frequencySum_pow {α : Type*} [Fintype α]
    (v : α → ι → ℤ) (w : α → ℂ) (p : ℕ) :
    Integrable (fun θ => ‖frequencySum v w θ‖ ^ p) (latticeHaar (ι := ι)) :=
  ((continuous_frequencySum v w).norm.pow p).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- A fourth power is the second moment of the actual pair-sum frequency family. -/
theorem frequencySum_sq {α : Type*} [Fintype α]
    (v : α → ι → ℤ) (w : α → ℂ) (θ : ι → AddCircle (1 : ℝ)) :
    frequencySum v w θ ^ 2 =
      frequencySum (fun p : α × α => v p.1 + v p.2) (fun p => w p.1 * w p.2) θ := by
  classical
  simp only [frequencySum, pow_two, Fintype.sum_prod_type, Finset.sum_mul,
    Finset.mul_sum, WaringSiegel.latticeCharacter_add]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Exact fourth moment, with all four roots and weights displayed. -/
theorem integral_norm_frequencySum_fourth {α : Type*} [Fintype α]
    (v : α → ι → ℤ) (w : α → ℂ) :
    (∫ θ, ‖frequencySum v w θ‖ ^ 4 ∂latticeHaar) =
      ∑ p : (α × α) × (α × α),
        if v p.1.1 + v p.1.2 = v p.2.1 + v p.2.2 then
          (w p.1.1 * w p.1.2 * conj (w p.2.1 * w p.2.2)).re else 0 := by
  have hp (θ : ι → AddCircle (1 : ℝ)) :
      ‖frequencySum v w θ‖ ^ 4 =
        ‖frequencySum (fun p : α × α => v p.1 + v p.2)
          (fun p => w p.1 * w p.2) θ‖ ^ 2 := by
    rw [← frequencySum_sq, norm_pow]
    ring
  simp_rw [hp]
  exact integral_norm_frequencySum_sq _ _

/-- Difference-frequency version of the fourth moment, matching the divisor argument. -/
theorem integral_norm_frequencySum_fourth_difference {α : Type*} [Fintype α]
    (v : α → ι → ℤ) (w : α → ℂ) :
    (∫ θ, ‖frequencySum v w θ‖ ^ 4 ∂latticeHaar) =
      ∫ θ, ‖frequencySum (fun p : α × α => v p.1 - v p.2)
        (fun p => w p.1 * conj (w p.2)) θ‖ ^ 2 ∂latticeHaar := by
  apply integral_congr_ae
  filter_upwards [] with θ
  have h := frequencySum_mul_conj_expansion v v w w θ
  change frequencySum v w θ * conj (frequencySum v w θ) =
    frequencySum (fun p : α × α => v p.1 - v p.2)
      (fun p => w p.1 * conj (w p.2)) θ at h
  rw [← h, norm_mul, Complex.norm_conj]
  ring

end WaringSiegel.WSL2
