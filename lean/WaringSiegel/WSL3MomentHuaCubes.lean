import WaringSiegel.WSL2MomentEighthReduction
import WaringSiegel.WSL3MomentHuaPolynomial

/-!
# All-order finite differencing on an additive lattice

The cube aggregate is a literal sum of characters over overlapping finite
sets.  At each positive order it is exactly a sum of squared norms from the
preceding order.  Thus no absolute values are inserted into individual
terms of the aggregate used by Hua's argument.
-/

noncomputable section
open Finset MeasureTheory
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

theorem sum_fin_function_succ {α T : Type*} [Fintype α] [AddCommMonoid T]
    (J : ℕ) (f : (Fin (J + 1) → α) → T) :
    (∑ h, f h) = ∑ t : Fin J → α, ∑ a : α, f (Fin.cons a t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (J + 1) => α)).sum_comp f,
    Fintype.sum_prod_type, Finset.sum_comm]
  rfl

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

def iteratedOverlap (S : Finset G) : (J : ℕ) → (Fin J → G) → Finset G
  | 0, _ => S
  | J + 1, h => additiveOverlap (iteratedOverlap S J (Fin.tail h)) (h 0)

def iteratedFrequency (v : G → ι → ℤ) : (J : ℕ) → (Fin J → G) → G → ι → ℤ
  | 0, _ => v
  | J + 1, h => fun x =>
      iteratedFrequency v J (Fin.tail h) (x + h 0) - iteratedFrequency v J (Fin.tail h) x

theorem iteratedOverlap_subset (S : Finset G) (J : ℕ) (h : Fin J → G) :
    iteratedOverlap S J h ⊆ S := by
  induction J with
  | zero => rfl
  | succ J ih => exact (additiveOverlap_subset _ _).trans (ih _)

def iteratedCubeSum (S H : Finset G) (J : ℕ) (v : G → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) : ℂ :=
  ∑ h : Fin J → H, finiteFrequencySum (iteratedOverlap S J (fun i => h i))
    (iteratedFrequency v J (fun i => h i)) θ

@[simp] theorem iteratedCubeSum_zero (S H : Finset G) (v : G → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    iteratedCubeSum S H 0 v θ = finiteFrequencySum S v θ := by
  simp [iteratedCubeSum, iteratedOverlap, iteratedFrequency]

/-- Exact successive autocorrelation, with one common finite shift set. -/
theorem iteratedCubeSum_succ (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (J : ℕ) (v : G → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    iteratedCubeSum S H (J + 1) v θ =
      ∑ h : Fin J → H,
        ((‖finiteFrequencySum (iteratedOverlap S J (fun i => h i))
          (iteratedFrequency v J (fun i => h i)) θ‖ ^ 2 : ℝ) : ℂ) := by
  unfold iteratedCubeSum
  rw [sum_fin_function_succ]
  apply Finset.sum_congr rfl
  intro h hh
  let T := iteratedOverlap S J (fun i => (h i : G))
  let f := iteratedFrequency v J (fun i => (h i : G))
  have hT : ∀ x ∈ T, ∀ y ∈ T, x - y ∈ H :=
    fun x hx y hy => hH x (iteratedOverlap_subset S J _ hx) y (iteratedOverlap_subset S J _ hy)
  have ha := finite_sum_norm_sq_autocorrelations T H hT (fun x => latticeCharacter (f x) θ)
  simp only [← latticeCharacter_sub] at ha
  change (∑ a : H, finiteFrequencySum (additiveOverlap T a)
    (fun x => f (x + a) - f x) θ) = _
  calc
    _ = ∑ a ∈ H, finiteFrequencySum (additiveOverlap T a) (fun x => f (x + a) - f x) θ :=
      (Finset.sum_subtype H (fun _ => Iff.rfl)
        (fun a => finiteFrequencySum (additiveOverlap T a) (fun x => f (x + a) - f x) θ)).symm
    _ = _ := ha.symm

theorem iteratedCubeSum_succ_re (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (J : ℕ) (v : G → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    (iteratedCubeSum S H (J + 1) v θ).re =
      ∑ h : Fin J → H,
        ‖finiteFrequencySum (iteratedOverlap S J (fun i => h i))
          (iteratedFrequency v J (fun i => h i)) θ‖ ^ 2 := by
  rw [iteratedCubeSum_succ S H hH]
  simp only [Complex.re_sum, Complex.ofReal_re]

theorem iteratedCubeSum_re_nonneg (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (J : ℕ) (hJ : 1 ≤ J)
    (v : G → ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    0 ≤ (iteratedCubeSum S H J v θ).re := by
  obtain ⟨J, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  rw [iteratedCubeSum_succ_re S H hH]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem iteratedCubeSum_cauchy (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (J : ℕ)
    (v : G → ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    (iteratedCubeSum S H J v θ).re ^ 2 ≤
      (H.card : ℝ) ^ J * (iteratedCubeSum S H (J + 1) v θ).re := by
  let f := fun h : Fin J → H => finiteFrequencySum (iteratedOverlap S J (fun i => h i))
    (iteratedFrequency v J (fun i => h i)) θ
  have hreal : (iteratedCubeSum S H J v θ).re ^ 2 ≤ ‖iteratedCubeSum S H J v θ‖ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  have htriangle := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le Finset.univ f) 2
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun h => ‖f h‖)
  have hnorm : ‖iteratedCubeSum S H J v θ‖ ^ 2 ≤
      (H.card : ℝ) ^ J * ∑ h, ‖f h‖ ^ 2 := by
    exact htriangle.trans (by simpa [Fintype.card_fun, f] using hcauchy)
  exact hreal.trans (by simpa only [iteratedCubeSum_succ_re S H hH] using hnorm)

theorem succ_le_two_pow (J : ℕ) : J + 1 ≤ 2 ^ J := by
  induction J with
  | zero => norm_num
  | succ J ih => rw [pow_succ]; omega

theorem cube_exponent_succ (J : ℕ) :
    2 ^ (J + 1) - (J + 1) - 1 = (2 ^ J - J - 1) * 2 + J := by
  have h := succ_le_two_pow J
  rw [pow_succ]
  omega

/-- The exact all-order Weyl differencing inequality needed by the Hua
induction.  The final character aggregate remains intact and nonnegative. -/
theorem finiteFrequencySum_pow_le_iteratedCube (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ H) (J : ℕ) (hJ : 1 ≤ J)
    (v : G → ι → ℤ) (θ : ι → AddCircle (1 : ℝ)) :
    ‖finiteFrequencySum S v θ‖ ^ (2 ^ J) ≤
      (H.card : ℝ) ^ (2 ^ J - J - 1) * (iteratedCubeSum S H J v θ).re := by
  induction J, hJ using Nat.le_induction with
  | base =>
    have h := iteratedCubeSum_succ_re S H hH 0 v θ
    simpa [iteratedOverlap, iteratedFrequency] using le_of_eq h.symm
  | succ J hJ ih =>
    calc
      ‖finiteFrequencySum S v θ‖ ^ (2 ^ (J + 1)) =
          (‖finiteFrequencySum S v θ‖ ^ (2 ^ J)) ^ 2 := by rw [pow_succ, pow_mul]
      _ ≤ ((H.card : ℝ) ^ (2 ^ J - J - 1) * (iteratedCubeSum S H J v θ).re) ^ 2 :=
        pow_le_pow_left₀ (by positivity) ih 2
      _ = (H.card : ℝ) ^ ((2 ^ J - J - 1) * 2) * (iteratedCubeSum S H J v θ).re ^ 2 := by
        rw [mul_pow, pow_mul]
      _ ≤ (H.card : ℝ) ^ ((2 ^ J - J - 1) * 2) *
          ((H.card : ℝ) ^ J * (iteratedCubeSum S H (J + 1) v θ).re) :=
        mul_le_mul_of_nonneg_left (iteratedCubeSum_cauchy S H hH J v θ) (by positivity)
      _ = _ := by rw [← mul_assoc, ← pow_add, ← cube_exponent_succ]

#print axioms iteratedCubeSum_cauchy
#print axioms finiteFrequencySum_pow_le_iteratedCube

end WaringSiegel.WSL3
