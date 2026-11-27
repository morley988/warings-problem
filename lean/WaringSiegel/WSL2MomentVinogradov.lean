import WaringSiegel.WSL2MomentBounds

/-!
# Literal full-system Vinogradov moments over algebraic integers

This module defines the actual k-fold frequency sum and its power-sum
equations, and proves weighted Haar orthogonality for every moment order.
No critical VMVT estimate is asserted or assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NumberField Classical

namespace WaringSiegel.WSL2
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem frequencySum_pow (v : α → ι → ℤ) (w : α → ℂ) (s : ℕ)
    (θ : ι → AddCircle (1 : ℝ)) :
    frequencySum v w θ ^ s =
      frequencySum (fun x : Fin s → α => ∑ i, v (x i)) (fun x => ∏ i, w (x i)) θ := by
  calc
    _ = ∏ _i : Fin s, ∑ a : α, w a * latticeCharacter (v a) θ := by simp [frequencySum]
    _ = ∑ x : Fin s → α, ∏ i, (w (x i) * latticeCharacter (v (x i)) θ) :=
      Fintype.prod_sum (fun (_i : Fin s) (a : α) => w a * latticeCharacter (v a) θ)
    _ = _ := by
      simp only [frequencySum, Finset.prod_mul_distrib, ← WaringSiegel.latticeCharacter_sum]

theorem integral_norm_frequencySum_even (v : α → ι → ℤ) (w : α → ℂ) (s : ℕ) :
    (∫ θ, ‖frequencySum v w θ‖^(2*s) ∂latticeHaar) =
      ∑ p : (Fin s → α) × (Fin s → α),
        if (∑ i, v (p.1 i)) = (∑ i, v (p.2 i)) then
          ((∏ i, w (p.1 i))*conj (∏ i, w (p.2 i))).re else 0 := by
  have hnorm (θ : ι → AddCircle (1 : ℝ)) :
      ‖frequencySum v w θ‖^(2*s) = ‖frequencySum v w θ ^ s‖^2 := by
    rw [norm_pow, ← pow_mul, Nat.mul_comm]
  simp_rw [hnorm, frequencySum_pow]
  exact integral_norm_frequencySum_sq _ _

theorem integral_norm_frequencySum_even_le_energy (v : α → ι → ℤ) (w : α → ℂ)
    (s : ℕ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖frequencySum v w θ‖^(2*s) ∂latticeHaar) ≤
      (frequencyEnergy (fun x : Fin s → α => ∑ i, v (x i)) : ℝ) * W^(2*s) := by
  have hnorm (θ : ι → AddCircle (1 : ℝ)) :
      ‖frequencySum v w θ‖^(2*s) = ‖frequencySum v w θ ^ s‖^2 := by
    rw [norm_pow, ← pow_mul, Nat.mul_comm]
  simp_rw [hnorm, frequencySum_pow]
  have h := integral_norm_frequencySum_sq_le_energy (fun x : Fin s → α => ∑ i, v (x i))
    (fun x => ∏ i, w (x i)) (W^s) (by positivity) (by
      intro x
      rw [norm_prod]
      calc
        _ ≤ ∏ i : Fin s, W := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hw (x i))
        _ = _ := by simp)
  convert h using 1
  rw [← pow_mul, Nat.mul_comm]

variable {R : Type*} [CommRing R]

def vinogradovFrequency (coord : R →+ (ι → ℤ)) (k : ℕ) (nodes : α → R)
    (x : α) : Fin k × ι → ℤ := fun ji => coord (nodes x ^ (ji.1.val+1)) ji.2

def VinogradovEquations (k s : ℕ) (nodes : α → R) (x y : Fin s → α) : Prop :=
  ∀ j : Fin k, (∑ i, nodes (x i) ^ (j.val+1)) = ∑ i, nodes (y i) ^ (j.val+1)

def vinogradovCount (k s : ℕ) (nodes : α → R) : ℕ :=
  (Finset.univ.filter (fun p : (Fin s → α) × (Fin s → α) =>
    VinogradovEquations k s nodes p.1 p.2)).card

theorem vinogradov_frequency_eq_iff (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (k s : ℕ) (nodes : α → R)
    (x y : Fin s → α) :
    (∑ i, vinogradovFrequency coord k nodes (x i)) =
      (∑ i, vinogradovFrequency coord k nodes (y i)) ↔ VinogradovEquations k s nodes x y := by
  constructor
  · intro heq j
    apply hcoord
    ext r
    have h := congrFun heq (j,r)
    simpa only [vinogradovFrequency, Finset.sum_apply, map_sum] using h
  · intro heq
    ext ji
    have h := congrArg (fun z => coord z ji.2) (heq ji.1)
    simpa only [vinogradovFrequency, Finset.sum_apply, map_sum] using h

/-- Exact weighted full-system mean-value identity, over the actual k-fold torus. -/
theorem integral_vinogradov_weighted (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (k s : ℕ) (nodes : α → R) (w : α → ℂ) :
    (∫ θ, ‖frequencySum (vinogradovFrequency coord k nodes) w θ‖^(2*s) ∂latticeHaar) =
      ∑ p : (Fin s → α) × (Fin s → α), if VinogradovEquations k s nodes p.1 p.2 then
        ((∏ i, w (p.1 i))*conj (∏ i, w (p.2 i))).re else 0 := by
  rw [integral_norm_frequencySum_even]
  simp only [vinogradov_frequency_eq_iff coord hcoord]

theorem integral_vinogradov_unweighted (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (k s : ℕ) (nodes : α → R) :
    (∫ θ, ‖frequencySum (vinogradovFrequency coord k nodes) (fun _ => 1) θ‖^(2*s) ∂latticeHaar) =
      (vinogradovCount k s nodes : ℝ) := by
  rw [integral_vinogradov_weighted coord hcoord]
  simp only [Finset.prod_const_one, map_one, mul_one, Complex.one_re]
  simp [vinogradovCount, Finset.sum_boole]

/-- Arbitrary bounded complex coefficients are controlled by the literal
unweighted solution count, not by an assumed Vinogradov bound. -/
theorem integral_vinogradov_le_count (coord : R →+ (ι → ℤ))
    (hcoord : Function.Injective coord) (k s : ℕ) (nodes : α → R) (w : α → ℂ)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖frequencySum (vinogradovFrequency coord k nodes) w θ‖^(2*s) ∂latticeHaar) ≤
      (vinogradovCount k s nodes : ℝ) * W^(2*s) := by
  have h := integral_norm_frequencySum_even_le_energy (vinogradovFrequency coord k nodes) w s W hW hw
  simpa only [frequencyEnergy, vinogradov_frequency_eq_iff coord hcoord, vinogradovCount] using h

/-- The fully literal algebraic-integer specialization. -/
theorem numberField_vinogradov_moment_le_count (K : Type*) [Field K] [NumberField K]
    {β : Type*} [Fintype β] (k s : ℕ) (nodes : β → 𝓞 K) (w : β → ℂ)
    (W : ℝ) (hW : 0 ≤ W) (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖frequencySum (vinogradovFrequency (integerCoordinates K) k nodes) w θ‖^(2*s)
      ∂latticeHaar) ≤ (vinogradovCount k s nodes : ℝ) * W^(2*s) :=
  integral_vinogradov_le_count (integerCoordinates K) (integerCoordinates_injective K) k s nodes w W hW hw

end WaringSiegel.WSL2
