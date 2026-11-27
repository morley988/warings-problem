import WaringSiegel.NormLattice
import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Exact transport by totally positive unit powers

Multiplication by the kth power of a totally positive unit preserves the
literal global target, including eligibility, every finite-place unit
coordinate, the sign of roots, and the root norm bound with the same constant.
-/

noncomputable section
open scoped NumberField BigOperators

namespace WaringSiegel.WSL2

variable {K : Type*} [Field K] [NumberField K]

theorem absNorm_mul (x y : 𝓞 K) : absNorm (x * y) = absNorm x * absNorm y := by
  simp only [absNorm, map_mul, Int.cast_mul, abs_mul]

theorem absNorm_pow (x : 𝓞 K) (k : ℕ) : absNorm (x ^ k) = absNorm x ^ k := by
  simp only [absNorm, map_pow, Int.cast_pow, abs_pow]

theorem absNorm_unit (u : (𝓞 K)ˣ) : absNorm (u : 𝓞 K) = 1 := by
  rw [← fieldAbsNorm_integer]
  unfold fieldAbsNorm
  have h := congrArg (fun q : ℚ => (q : ℝ)) (NumberField.Units.norm K u)
  simpa only [Rat.cast_abs, Rat.cast_one] using h

theorem absNorm_unit_mul (u : (𝓞 K)ˣ) (ν : 𝓞 K) :
    absNorm ((u : 𝓞 K) * ν) = absNorm ν := by
  rw [absNorm_mul, absNorm_unit, one_mul]

theorem absNorm_unit_pow_mul (u : (𝓞 K)ˣ) (k : ℕ) (ν : 𝓞 K) :
    absNorm ((u : 𝓞 K) ^ k * ν) = absNorm ν := by
  rw [absNorm_mul, absNorm_pow, absNorm_unit, one_pow, one_mul]

theorem totallyPositive_mul {x y : 𝓞 K}
    (hx : TotallyPositive x) (hy : TotallyPositive y) : TotallyPositive (x * y) := by
  intro σ
  simpa only [map_mul] using mul_pos (hx σ) (hy σ)

theorem totallyPositive_pow {x : 𝓞 K} (hx : TotallyPositive x) (k : ℕ) :
    TotallyPositive (x ^ k) := by
  intro σ
  simpa only [map_pow] using pow_pos (hx σ) k

theorem totallyNonnegative_mul_of_positive {x y : 𝓞 K}
    (hx : TotallyPositive x) (hy : TotallyNonnegative y) : TotallyNonnegative (x * y) := by
  intro σ
  simpa only [map_mul] using mul_nonneg (hx σ).le (hy σ)

theorem totallyPositive_unit_inv (u : (𝓞 K)ˣ) (hu : TotallyPositive (u : 𝓞 K)) :
    TotallyPositive (↑(u⁻¹) : 𝓞 K) := by
  intro σ
  have h := map_units_inv (σ.comp (algebraMap (𝓞 K) K)) u
  change σ ((↑(u⁻¹) : 𝓞 K) : K) = (σ ((u : 𝓞 K) : K))⁻¹ at h
  rw [h]
  exact inv_pos.mpr (hu σ)

/-- Squaring any unit produces a totally positive unit, including in fields
with real places of arbitrary signature. -/
theorem totallyPositive_unit_sq (u : (𝓞 K)ˣ) :
    TotallyPositive (↑(u ^ 2) : 𝓞 K) := by
  intro σ
  have hn : σ ((u : 𝓞 K) : K) ≠ 0 :=
    (map_ne_zero σ).mpr (NumberField.Units.coe_ne_zero u)
  simpa only [Units.val_pow_eq_pow_val, map_pow] using sq_pos_of_ne_zero hn

theorem eligible_mul_power {k : ℕ} {ν : 𝓞 K} (hν : Eligible k ν) (x : 𝓞 K) :
    Eligible k (x ^ k * ν) := by
  let f : 𝓞 K →+ 𝓞 K := AddMonoidHom.mulLeft (x ^ k)
  have hle : powerSubgroup (K := K) k ≤ (powerSubgroup k).comap f := by
    apply (AddSubgroup.closure_le _).mpr
    rintro y ⟨z, rfl⟩
    change x ^ k * z ^ k ∈ powerSubgroup k
    rw [← mul_pow]
    exact AddSubgroup.subset_closure ⟨x * z, rfl⟩
  exact hle hν

theorem eligible_unit_pow_iff (u : (𝓞 K)ˣ) (k : ℕ) (ν : 𝓞 K) :
    Eligible k ((u : 𝓞 K) ^ k * ν) ↔ Eligible k ν := by
  constructor
  · intro h
    have hi := eligible_mul_power h (↑(u⁻¹) : 𝓞 K)
    simpa only [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul] using hi
  · exact fun h => eligible_mul_power h u

theorem localUnitSolvable_mul_unit_pow {k s : ℕ} {ν : 𝓞 K}
    (hν : LocalUnitSolvable k s ν) (u : (𝓞 K)ˣ) :
    LocalUnitSolvable k s ((u : 𝓞 K) ^ k * ν) := by
  intro v
  obtain ⟨x, hx, i, hi⟩ := hν v
  let f := algebraMap (𝓞 K) (v.adicCompletionIntegers K)
  refine ⟨fun j => f u * x j, ?_, i, (u.isUnit.map f).mul hi⟩
  simp only [mul_pow, ← Finset.mul_sum, hx, map_mul, map_pow]
  rfl

theorem localUnitSolvable_unit_pow_iff (u : (𝓞 K)ˣ) (k s : ℕ) (ν : 𝓞 K) :
    LocalUnitSolvable k s ((u : 𝓞 K) ^ k * ν) ↔ LocalUnitSolvable k s ν := by
  constructor
  · intro h
    have hi := localUnitSolvable_mul_unit_pow h u⁻¹
    simpa only [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul] using hi
  · exact fun h => localUnitSolvable_mul_unit_pow h u

theorem representable_mul_unit_pow {k s : ℕ} {C : ℝ} {ν : 𝓞 K}
    (hν : RepresentableByAtMost k s C ν) (u : (𝓞 K)ˣ)
    (hu : TotallyPositive (u : 𝓞 K)) :
    RepresentableByAtMost k s C ((u : 𝓞 K) ^ k * ν) := by
  obtain ⟨t, ht, x, hx, hsum, hnorm⟩ := hν
  refine ⟨t, ht, fun i => (u : 𝓞 K) * x i,
    fun i => totallyNonnegative_mul_of_positive hu (hx i), ?_, ?_⟩
  · simp only [mul_pow, ← Finset.mul_sum, hsum]
  · intro i
    rw [absNorm_unit_mul, absNorm_unit_pow_mul]
    exact hnorm i

/-- The same representation constant survives normalizing and undoing the unit. -/
theorem representable_unit_pow_iff (u : (𝓞 K)ˣ)
    (hu : TotallyPositive (u : 𝓞 K)) (k s : ℕ) (C : ℝ) (ν : 𝓞 K) :
    RepresentableByAtMost k s C ((u : 𝓞 K) ^ k * ν) ↔
      RepresentableByAtMost k s C ν := by
  constructor
  · intro h
    have hi := representable_mul_unit_pow h u⁻¹ (totallyPositive_unit_inv u hu)
    simpa only [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul] using hi
  · exact fun h => representable_mul_unit_pow h u hu

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.representable_unit_pow_iff
#print axioms WaringSiegel.WSL2.eligible_unit_pow_iff
#print axioms WaringSiegel.WSL2.localUnitSolvable_unit_pow_iff
