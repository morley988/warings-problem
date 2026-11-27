import Waring.AuxiliaryL2Grouping

/-!
# Divisor-marked auxiliary energy

In the bad-factor branch the auxiliary sum is restricted by r dividing a
nonzero derivative value. After squaring and integrating, a collision can
occur only for common divisors of the two derivative values. Counting these
marks gives an actual uniform P^epsilon loss by the proved divisor bound.
-/

noncomputable section
open scoped BigOperators
namespace Waring.DivisorMarkedEnergy
open AuxiliaryL2Grouping

theorem marked_collision_set {ι : Type*} (A : Finset ι) (f : ι → ℤ)
    (D : ι → ℕ) (r : ℕ) :
    collisionPairs (A.filter (fun x => r ∣ D x)) f =
      (collisionPairs A f).filter (fun p => r ∣ D p.1 ∧ r ∣ D p.2) := by
  classical
  ext p
  simp only [collisionPairs,Finset.mem_filter,Finset.mem_product]
  tauto

/-- Exact interchange of the divisor mark and the original frequency collision. -/
theorem sum_marked_collision_card {ι : Type*} (K : Finset ℕ) (A : Finset ι)
    (f : ι → ℤ) (D : ι → ℕ) :
    (∑ r ∈ K, (collisionPairs (A.filter (fun x => r ∣ D x)) f).card) =
      ∑ p ∈ collisionPairs A f, (K.filter (fun r => r ∣ D p.1 ∧ r ∣ D p.2)).card := by
  classical
  simp_rw [marked_collision_set,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]

/-- A finite uniform divisor bound controls the entire marked energy. -/
theorem sum_marked_collision_le {ι : Type*} (K : Finset ℕ) (A : Finset ι)
    (f : ι → ℤ) (D : ι → ℕ) {T : ℝ}
    (hD : ∀ x ∈ A, 0 < D x ∧ ((D x).divisors.card : ℝ) ≤ T) :
    (∑ r ∈ K, ((collisionPairs (A.filter (fun x => r ∣ D x)) f).card : ℝ)) ≤
      T*((collisionPairs A f).card : ℝ) := by
  classical
  have heq : (∑ r ∈ K, ((collisionPairs (A.filter (fun x => r ∣ D x)) f).card : ℝ)) =
      ∑ p ∈ collisionPairs A f,
        ((K.filter (fun r => r ∣ D p.1 ∧ r ∣ D p.2)).card : ℝ) := by
    exact_mod_cast sum_marked_collision_card K A f D
  rw [heq]
  calc
    _ ≤ ∑ _p ∈ collisionPairs A f, T := by
      apply Finset.sum_le_sum
      intro p hp
      have hpA := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      have hsub : K.filter (fun r => r ∣ D p.1 ∧ r ∣ D p.2) ⊆ (D p.1).divisors := by
        intro r hr
        exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hr).2.1,(hD p.1 hpA).1.ne'⟩
      exact (by exact_mod_cast Finset.card_le_card hsub :
        ((K.filter (fun r => r ∣ D p.1 ∧ r ∣ D p.2)).card : ℝ) ≤
          ((D p.1).divisors.card : ℝ)).trans (hD p.1 hpA).2
    _ = T*((collisionPairs A f).card : ℝ) := by simp [mul_comm]

/-- Divisor estimates discharge the actual mark multiplicity uniformly. -/
theorem sum_marked_collision_le_rpow {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ (ι : Type*)
      (K : Finset ℕ) (A : Finset ι) (f : ι → ℤ) (D : ι → ℕ),
      (∀ x ∈ A, 0 < D x ∧ (D x : ℝ) ≤ P^B) →
      (∑ r ∈ K, ((collisionPairs (A.filter (fun x => r ∣ D x)) f).card : ℝ)) ≤
        C*P^ε*((collisionPairs A f).card : ℝ) := by
  let δ : ℝ := ε/(B+1)
  have hden : 0 < B+1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨C,hC,hdiv⟩ := DivisorBound.divisor_count_le_rpow hδ
  refine ⟨C,hC,?_⟩
  intro P hP ι K A f D hD
  apply sum_marked_collision_le K A f D
  intro x hx
  refine ⟨(hD x hx).1,?_⟩
  have hBδ : B*δ ≤ ε := by
    have hid : δ*(B+1)=ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  calc
    ((D x).divisors.card : ℝ) ≤ C*(D x : ℝ)^δ := hdiv _ (hD x hx).1
    _ ≤ C*(P^B)^δ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hD x hx).2 hδ.le) hC.le
    _ = C*P^(B*δ) := by rw [← Real.rpow_mul (zero_le_one.trans hP)]
    _ ≤ C*P^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hP hBδ) hC.le

/-- The same proved bound for the actual square-norm integrals. -/
theorem sum_marked_integral_le_rpow {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ (ι : Type*)
      (K : Finset ℕ) (A : Finset ι) (f : ι → ℤ) (D : ι → ℕ),
      (∀ x ∈ A, 0 < D x ∧ (D x : ℝ) ≤ P^B) →
      (∑ r ∈ K, (∫ α in (0 : ℝ)..1,
        ‖∑ x ∈ A.filter (fun x => r ∣ D x), fourier (f x) (α : AddCircle (1 : ℝ))‖^2)) ≤
        C*P^ε*(∫ α in (0 : ℝ)..1,
          ‖∑ x ∈ A, fourier (f x) (α : AddCircle (1 : ℝ))‖^2) := by
  obtain ⟨C,hC,hbound⟩ := sum_marked_collision_le_rpow hB hε
  refine ⟨C,hC,?_⟩
  intro P hP ι K A f D hD
  simp_rw [interval_integral_sq_norm_eq_collision_count]
  exact hbound P hP ι K A f D hD

#print axioms sum_marked_collision_card
#print axioms sum_marked_integral_le_rpow
end Waring.DivisorMarkedEnergy
