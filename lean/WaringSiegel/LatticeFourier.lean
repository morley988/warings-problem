import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Exact Fourier coefficient extraction on an integer-coordinate lattice

An integral basis identifies the additive group of a number-field integer ring
with an integer-coordinate lattice.  This file proves the actual Haar-integral
orthogonality and the finite weighted representation-count identity on its
coordinate torus.  There is no assumed orthogonality or assumed count formula.

The analytic estimates for the major and minor arcs are separate obligations.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace WaringSiegel

local instance onePeriodPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {ι : Type*} [Fintype ι]

/-- Probability Haar measure on the coordinate torus of a rank-`ι` lattice. -/
def latticeHaar : Measure (ι → AddCircle (1 : ℝ)) :=
  Measure.pi (fun _ : ι => AddCircle.haarAddCircle)

/-- The character with integer frequency `m`, evaluated on the coordinate torus. -/
def latticeCharacter (m : ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) : ℂ :=
  ∏ i, fourier (m i) (θ i)

theorem integral_fourier_unit_period (m : ℤ) :
    (∫ θ : AddCircle (1 : ℝ), fourier m θ ∂AddCircle.haarAddCircle) =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp only [fourier_zero]
    simp
  · rw [if_neg hm]
    exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hm zero_lt_one)

theorem latticeCharacter_integrable (m : ι → ℤ) :
    Integrable (latticeCharacter m) (latticeHaar (ι := ι)) := by
  apply Integrable.fintype_prod
  intro i
  exact (fourier (T := (1 : ℝ)) (m i)).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Actual Haar orthogonality in every finite lattice rank. -/
theorem latticeCharacter_orthogonality (m : ι → ℤ) :
    (∫ θ, latticeCharacter m θ ∂latticeHaar) = if m = 0 then 1 else 0 := by
  classical
  unfold latticeCharacter latticeHaar
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_fourier_unit_period]
  by_cases hm : m = 0
  · subst m
    simp
  · rw [if_neg hm]
    have hnot : ¬ ∀ i, m i = 0 := fun h => hm (funext h)
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Integrating a finite weighted character sum extracts exactly the terms
having the specified lattice frequency. -/
theorem integral_weighted_lattice_sum
    {α : Type*} (S : Finset α) (w : α → ℂ) (v : α → ι → ℤ) (target : ι → ℤ) :
    (∫ θ, ∑ a ∈ S, w a * latticeCharacter (v a - target) θ ∂latticeHaar) =
      ∑ a ∈ S, if v a = target then w a else 0 := by
  classical
  rw [integral_finset_sum S
    (fun a _ => (latticeCharacter_integrable (v a - target)).const_mul (w a))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_const_mul, latticeCharacter_orthogonality]
  simp only [sub_eq_zero, mul_ite, mul_one, mul_zero]

/-- A literal weighted count of sums of powers in any ring whose additive group
has injective integer coordinates, in particular an algebraic integer ring
after choosing an integral basis. -/
theorem integral_power_representation_count
    {A : Type*} [CommRing A] [DecidableEq A]
    (coord : A →+ (ι → ℤ)) (hcoord : Function.Injective coord)
    (k s : ℕ) (S : Finset (Fin s → A)) (w : (Fin s → A) → ℂ) (ν : A) :
    (∫ θ, ∑ x ∈ S,
        w x * latticeCharacter (coord (∑ i, x i ^ k) - coord ν) θ ∂latticeHaar) =
      ∑ x ∈ S, if (∑ i, x i ^ k) = ν then w x else 0 := by
  classical
  rw [integral_weighted_lattice_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [hcoord.eq_iff]

/-- A nonzero Fourier coefficient supplies an actual tuple solving the power
equation.  Proving that the coefficient is nonzero is the analytic endgame. -/
theorem power_representation_of_integral_ne_zero
    {A : Type*} [CommRing A]
    (coord : A →+ (ι → ℤ)) (hcoord : Function.Injective coord)
    (k s : ℕ) (S : Finset (Fin s → A)) (w : (Fin s → A) → ℂ) (ν : A)
    (h : (∫ θ, ∑ x ∈ S,
      w x * latticeCharacter (coord (∑ i, x i ^ k) - coord ν) θ ∂latticeHaar) ≠ 0) :
    ∃ x ∈ S, (∑ i, x i ^ k) = ν := by
  classical
  rw [integral_power_representation_count coord hcoord] at h
  by_contra hnone
  apply h
  apply Finset.sum_eq_zero
  intro x hx
  have hne : (∑ i, x i ^ k) ≠ ν := fun hsum => hnone ⟨x, hx, hsum⟩
  simp only [if_neg hne]

/-- The coordinate-injectivity condition is discharged by any integral basis. -/
theorem integral_power_representation_count_of_basis
    {A : Type*} [CommRing A] [DecidableEq A] (b : Module.Basis ι ℤ A)
    (k s : ℕ) (S : Finset (Fin s → A)) (w : (Fin s → A) → ℂ) (ν : A) :
    (∫ θ, ∑ x ∈ S,
        w x * latticeCharacter (b.equivFun (∑ i, x i ^ k) - b.equivFun ν) θ ∂latticeHaar) =
      ∑ x ∈ S, if (∑ i, x i ^ k) = ν then w x else 0 := by
  exact integral_power_representation_count b.equivFun.toLinearMap.toAddMonoidHom
    b.equivFun.injective k s S w ν

end WaringSiegel
