import Waring.PolynomialSumReduction
import Waring.FourierCompletionMoments
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact separation of coefficient variables after ordinary differencing

The coefficient tuple is summed before any absolute value is taken. A
Cartesian product of its independent coefficient sets therefore factors
exactly into the degree-sixteen/eighteen sums in the manuscript. The
quadratic interval and parity class have already become independent of
this tuple. Completion then uses one common real linear modulation for
the whole remaining shift family.
-/

noncomputable section
open scoped BigOperators
namespace Waring.CoefficientFactorization
open PolynomialSumReduction QuadraticModulation FourierCompletion

def coefficientSum (p : ℕ) (C : Finset ℝ) (β : ℝ) : ℂ :=
  ∑ m ∈ C, e (β*m^p)

def coefficientProduct {j : ℕ} (p : ℕ) (C : Fin j → Finset ℝ)
    (h : Fin j → ℝ) (β : ℝ) : ℂ :=
  ∏ i, coefficientSum p (C i) (β*(h i)^2)

def quadraticSum (S : Finset ℤ) (β t : ℝ) : ℂ :=
  ∑ ξ ∈ S, e (β*(ξ:ℝ)^2+t*(ξ:ℝ))

def coefficientWeight {j : ℕ} (p : ℕ) (A Γ U α : ℝ)
    (C : Fin j → Finset ℝ) (h : Fin j → ℝ) (ξ : ℤ) : ℂ :=
  ∑ m ∈ Fintype.piFinset C, e (α*normalForm p A Γ U h m (ξ:ℝ))

theorem e_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    e (∑ i ∈ s, f i) = ∏ i ∈ s, e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [e]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, e_add, ih]

theorem normalForm_phase_factor {j : ℕ} (p : ℕ) (A Γ U α : ℝ)
    (h m : Fin j → ℝ) (ξ : ℝ) :
    e (α*normalForm p A Γ U h m ξ) =
      e (α*A*Γ*U)*e ((3*α*A*Γ)*ξ^2)*
        ∏ i, e ((4*α*A*Γ)*(h i)^2*(m i)^p) := by
  have heq : α*normalForm p A Γ U h m ξ =
      α*A*Γ*U+(3*α*A*Γ)*ξ^2+
        ∑ i, (4*α*A*Γ)*(h i)^2*(m i)^p := by
    simp only [normalForm, coefficientPolynomial]
    rw [show (∑ i, (4*α*A*Γ)*(h i)^2*(m i)^p) =
      (4*α*A*Γ)*(∑ i, (h i)^2*(m i)^p) by simp only [Finset.mul_sum, mul_assoc]]
    ring
  rw [heq, e_add, e_add, e_finset_sum]

/-- Exact coefficient factorization. No triangle inequality has touched any
coefficient variable. -/
theorem coefficientWeight_eq {j : ℕ} (p : ℕ) (A Γ U α : ℝ)
    (C : Fin j → Finset ℝ) (h : Fin j → ℝ) (ξ : ℤ) :
    coefficientWeight p A Γ U α C h ξ =
      e (α*A*Γ*U)*e ((3*α*A*Γ)*(ξ:ℝ)^2)*
        coefficientProduct p C h (4*α*A*Γ) := by
  classical
  unfold coefficientWeight coefficientProduct coefficientSum
  simp_rw [normalForm_phase_factor]
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.prod_univ_sum C (fun i x => e ((4*α*A*Γ)*(h i)^2*x^p))).symm

/-- The actual Cartesian coefficient-and-quadratic sum factors exactly. -/
theorem coefficient_interval_sum_factor {j : ℕ} (p : ℕ) (A Γ U α : ℝ)
    (C : Fin j → Finset ℝ) (h : Fin j → ℝ) (S : Finset ℤ) :
    (∑ m ∈ Fintype.piFinset C, ∑ ξ ∈ S,
      e (α*normalForm p A Γ U h m (ξ:ℝ))) =
      e (α*A*Γ*U)*quadraticSum S (3*α*A*Γ) 0*
        coefficientProduct p C h (4*α*A*Γ) := by
  classical
  rw [Finset.sum_comm]
  change (∑ ξ ∈ S, coefficientWeight p A Γ U α C h ξ) = _
  simp_rw [coefficientWeight_eq]
  simp only [quadraticSum, zero_mul, add_zero, Finset.mul_sum, Finset.sum_mul]

theorem coefficient_interval_norm_factor {j : ℕ} (p : ℕ) (A Γ U α : ℝ)
    (C : Fin j → Finset ℝ) (h : Fin j → ℝ) (S : Finset ℤ) :
    ‖∑ m ∈ Fintype.piFinset C, ∑ ξ ∈ S,
      e (α*normalForm p A Γ U h m (ξ:ℝ))‖ =
      ‖quadraticSum S (3*α*A*Γ) 0‖ *
        ∏ i, ‖coefficientSum p (C i) ((4*α*A*Γ)*(h i)^2)‖ := by
  rw [coefficient_interval_sum_factor]
  simp only [norm_mul, norm_e, one_mul, coefficientProduct, norm_prod]

theorem modulated_coefficientWeight {j : ℕ} (p : ℕ) (A Γ U α : ℝ)
    (C : Fin j → Finset ℝ) (h : Fin j → ℝ) (S : Finset ℤ) (t : ℝ) :
    modulatedSum S (coefficientWeight p A Γ U α C h) t =
      e (α*A*Γ*U)*quadraticSum S (3*α*A*Γ) t*
        coefficientProduct p C h (4*α*A*Γ) := by
  unfold modulatedSum
  simp_rw [coefficientWeight_eq]
  simp only [quadraticSum, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [show fourier ξ (t : AddCircle (1:ℝ)) = e (t*(ξ:ℝ)) by
    exact (exp_linear_eq_fourier t ξ).symm, e_add]
  ring

/-- Completion preserves one common real modulation t for the quadratic
sum, and the coefficient sums are unchanged. -/
theorem norm_modulated_coefficientWeight {j : ℕ} (p : ℕ) (A Γ U α : ℝ)
    (C : Fin j → Finset ℝ) (h : Fin j → ℝ) (S : Finset ℤ) (t : ℝ) :
    ‖modulatedSum S (coefficientWeight p A Γ U α C h) t‖ =
      ‖quadraticSum S (3*α*A*Γ) t‖ *
        ∏ i, ‖coefficientSum p (C i) ((4*α*A*Γ)*(h i)^2)‖ := by
  rw [modulated_coefficientWeight]
  simp only [norm_mul, norm_e, one_mul, coefficientProduct, norm_prod]

/-- The manuscript's completed-product bound. The sole remaining estimate
is the explicitly displayed common-t product sum; factorization, parity
completion, and its logarithmic loss are proved here. -/
theorem completed_product_bound {ι : Type*} {j : ℕ} (s : Finset ι)
    (p : ℕ) (A α : ℝ) (Γ U : ι → ℝ) (C : ι → Fin j → Finset ℝ)
    (h : ι → Fin j → ℝ) (a b r : ι → ℤ) (S : Finset ℤ) (N : ℕ)
    (hN : 0 < N)
    (hlen : ∀ i ∈ s, (b i+1-a i).toNat ≤ N)
    (hsub : ∀ i ∈ s, (Finset.Icc (a i) (b i)).filter (fun ξ => ξ%2=r i%2) ⊆ S)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ Set.Icc (0:ℝ) 1,
      (∑ i ∈ s, ‖quadraticSum S (3*α*A*Γ i) t‖ *
        ∏ l, ‖coefficientSum p (C i l) ((4*α*A*Γ i)*(h i l)^2)‖) ≤ B) :
    ‖∑ i ∈ s, ∑ m ∈ Fintype.piFinset (C i),
      ∑ ξ ∈ (Finset.Icc (a i) (b i)).filter (fun ξ => ξ%2=r i%2),
        e (α*normalForm p A (Γ i) (U i) (h i) m (ξ:ℝ))‖ ≤
      (4*(2+Real.log (N:ℝ)/Real.log 2))*B := by
  classical
  have H := family_parity_moment_log_bound s S a b r
    (fun i => coefficientWeight p A (Γ i) (U i) α (C i) (h i)) N 1 hN (by norm_num)
    hlen hsub B hB0 (by
      intro t ht
      simpa only [pow_one, norm_modulated_coefficientWeight] using hB t ht)
  simp only [pow_one] at H
  apply (norm_sum_le _ _).trans
  calc
    _ = ∑ i ∈ s, ‖∑ ξ ∈ (Finset.Icc (a i) (b i)).filter (fun ξ => ξ%2=r i%2),
      coefficientWeight p A (Γ i) (U i) α (C i) (h i) ξ‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact Finset.sum_comm
    _ ≤ _ := H

#print axioms coefficient_interval_sum_factor
#print axioms norm_modulated_coefficientWeight
#print axioms completed_product_bound

end Waring.CoefficientFactorization
