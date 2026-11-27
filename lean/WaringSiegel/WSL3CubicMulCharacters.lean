import WaringSiegel.WSL3CubicGauss
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # WSL3: finite-field multiplicative Fourier orthogonality -/
noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace WaringSiegel
variable {F : Type*} [Field F] [Fintype F]

theorem finite_field_units_sum_eq (f : F → ℂ) :
    (∑ u : Fˣ, f u) = (∑ x : F, f x) - f 0 := by
  classical
  trans ∑ x ∈ (Finset.univ.erase (0 : F)), f x
  · apply Finset.sum_bij (fun (x : Fˣ) _ => (x : F))
    · intro x _; simp only [Finset.mem_erase, Finset.mem_univ, and_true]; exact Units.ne_zero x
    · intro x _ y _ h; exact Units.ext h
    · intro x hx; exact ⟨Units.mk0 x (Finset.mem_erase.mp hx).1, Finset.mem_univ _, rfl⟩
    · intro x _; rfl
  · exact Finset.sum_erase_eq_sub (Finset.mem_univ (0 : F))

theorem finite_field_mulChar_units_sum (χ : MulChar F ℂ) :
    (∑ u : Fˣ, χ u) = if χ = 1 then (Fintype.card Fˣ : ℂ) else 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ; simp
  · rw [if_neg hχ, finite_field_units_sum_eq, χ.sum_eq_zero_of_ne_one hχ, χ.map_zero, sub_zero]


theorem finite_field_mulChar_power_units_sum (χ : MulChar F ℂ) (k : ℕ) :
    (∑ u : Fˣ, χ ((u : F)^k)) =
      if χ^k = 1 then (Fintype.card Fˣ : ℂ) else 0 := by
  simpa only [map_pow, MulChar.pow_apply_coe] using
    finite_field_mulChar_units_sum (χ^k)

section Dual
variable [Fintype (MulChar F ℂ)]

theorem finite_field_mulChar_card :
    Fintype.card (MulChar F ℂ) = Fintype.card Fˣ := by
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity F ℂ

theorem finite_field_mulChar_orthogonality (u : Fˣ) :
    (∑ χ : MulChar F ℂ, χ u) = if u = 1 then (Fintype.card Fˣ : ℂ) else 0 := by
  classical
  by_cases hu : u = 1
  · subst u
    simp [finite_field_mulChar_card]
  · rw [if_neg hu]
    have hu' : (u : F) ≠ 1 := fun h => hu (Units.ext h)
    obtain ⟨χ, hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity F ℂ hu'
    apply eq_zero_of_mul_eq_self_left hχ
    simpa only [Finset.mul_sum, ← MulChar.mul_apply] using
      (Equiv.mulLeft χ).bijective.sum_comp (fun ψ : MulChar F ℂ => ψ u)


/-- Fourier expansion on the actual multiplicative group of the field. -/
theorem finite_field_mulChar_fourier_expansion (f : Fˣ → ℂ) (u : Fˣ) :
    (Fintype.card Fˣ : ℂ) * f u =
      ∑ χ : MulChar F ℂ, ∑ v : Fˣ, f v * χ ((v / u : Fˣ) : F) := by
  classical
  symm
  calc
    _ = ∑ v : Fˣ, f v * ∑ χ : MulChar F ℂ, χ ((v / u : Fˣ) : F) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = ∑ v : Fˣ, f v * (if v = u then (Fintype.card Fˣ : ℂ) else 0) := by
      simp only [finite_field_mulChar_orthogonality, div_eq_one]
    _ = (Fintype.card Fˣ : ℂ) * f u := by
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

theorem finite_field_mulChar_power_ratio_sum (χ : MulChar F ℂ) (v : Fˣ) (k : ℕ) :
    (∑ u : Fˣ, χ ((v / u^k : Fˣ) : F)) =
      χ v * (if χ^k = 1 then (Fintype.card Fˣ : ℂ) else 0) := by
  classical
  calc
    _ = χ v * ∑ u : Fˣ, χ (((u⁻¹ : Fˣ) : F)^k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      simp only [div_eq_mul_inv, ← inv_pow, Units.val_mul, Units.val_pow_eq_pow_val,
        map_mul]
    _ = χ v * ∑ u : Fˣ, χ ((u : F)^k) := by
      congr 1
      exact (Equiv.inv Fˣ).bijective.sum_comp (fun u : Fˣ => χ ((u : F)^k))
    _ = _ := by rw [finite_field_mulChar_power_units_sum]

theorem finite_field_mulChar_power_expansion (f : Fˣ → ℂ) (k : ℕ) :
    (∑ u : Fˣ, f (u^k)) =
      ∑ χ : MulChar F ℂ, if χ^k = 1 then ∑ v : Fˣ, f v * χ v else 0 := by
  classical
  have hcard : (Fintype.card Fˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply mul_left_cancel₀ hcard
  calc
    _ = ∑ u : Fˣ, ∑ χ : MulChar F ℂ, ∑ v : Fˣ, f v * χ ((v / u^k : Fˣ) : F) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      exact finite_field_mulChar_fourier_expansion f (u^k)
    _ = ∑ χ : MulChar F ℂ, ∑ v : Fˣ,
        f v * (χ v * (if χ^k = 1 then (Fintype.card Fˣ : ℂ) else 0)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum, finite_field_mulChar_power_ratio_sum]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      split_ifs with hχ
      · simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
      · simp

end Dual
end WaringSiegel
