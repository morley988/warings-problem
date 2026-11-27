import Waring.RestrictedSmoothShorterMoments
import Waring.RestrictedSmoothArcReduction

/-! # Actual moment bound for the complete ordered-block sum -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothArcs
open SmoothMoments RestrictedSmoothFactorization

theorem blockMomentSum_epsilon {k s : ℕ} {lam ε : ℝ}
    (hadm : AdmissibleExponent k s lam) (hlam : 1 ≤ lam) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ R : ℝ,1 ≤ R → R ≤ P^η → ∀ M : ℝ,1 ≤ M → M*R ≤ P →
        blockMomentSum k s P R M ≤ C*P^ε*(M*R)*(P/M)^lam/M^k := by
  obtain ⟨η,hη,A,hA,hbound⟩ := sum_shorter_moments_epsilon hadm hlam hε
  refine ⟨η,hη,A,hA,?_⟩
  intro P hP R hR hRP M hM hMR
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hMp : 0 < M := zero_lt_one.trans_le hM
  have hMR0 : 0 ≤ M*R := by positivity
  have hpoint (b : ℕ × ℕ) (hb : b ∈ orderedBlocks M R) :
      ((b.2 : ℝ)^k)⁻¹*(∑ z ∈ smoothNumbers (P/(b.2 : ℝ)) R,
        smoothMoment k s ((P/(b.2 : ℝ))/(z : ℝ)) b.1) ≤ A*P^ε*(P/M)^lam/M^k := by
    obtain ⟨hm,hMm,hmMR,hπR⟩ := orderedBlocks_bounds hM hR hb
    have hm1 : (1 : ℝ) ≤ b.2 := by exact_mod_cast hm
    have hmp : 0 < (b.2 : ℝ) := zero_lt_one.trans_le hm1
    have hπ1 : 1 ≤ b.1 := by
      classical
      exact (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).1).1.trans' (by norm_num)
    have hX1 : 1 ≤ P/(b.2 : ℝ) := (one_le_div hmp).mpr (hmMR.trans hMR)
    have hXP : P/(b.2 : ℝ) ≤ P := div_le_self hP0 hm1
    have hdiv : P/(b.2 : ℝ) ≤ P/M := div_le_div_of_nonneg_left hP0 hMp hMm.le
    have hinv : ((b.2 : ℝ)^k)⁻¹ ≤ (M^k)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hMp k)
        (pow_le_pow_left₀ hMp.le hMm.le k)
    have hp : (P/(b.2 : ℝ))^lam ≤ (P/M)^lam :=
      Real.rpow_le_rpow (by positivity) hdiv (zero_le_one.trans hlam)
    calc
      _ ≤ ((b.2 : ℝ)^k)⁻¹*(A*P^ε*(P/(b.2 : ℝ))^lam) :=
        mul_le_mul_of_nonneg_left (hbound P hP R hR hRP _ hX1 hXP b.1 hπ1 hπR) (by positivity)
      _ ≤ (M^k)⁻¹*(A*P^ε*(P/M)^lam) := mul_le_mul hinv
        (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ b ∈ orderedBlocks M R,A*P^ε*(P/M)^lam/M^k := Finset.sum_le_sum hpoint
    _ = ((orderedBlocks M R).card : ℝ)*(A*P^ε*(P/M)^lam/M^k) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (M*R)*(A*P^ε*(P/M)^lam/M^k) :=
      mul_le_mul_of_nonneg_right (orderedBlocks_card_le hM hMR0) (by positivity)
    _ = _ := by ring

theorem weighted_blockMomentSum_epsilon {k s : ℕ} (hs : 1 ≤ s) {lam ε : ℝ}
    (hadm : AdmissibleExponent k s lam) (hlam : 1 ≤ lam) (hε : 0 < ε) :
    ∃ η : ℝ,0 < η ∧ ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P →
      ∀ R : ℝ,1 ≤ R → R ≤ P^η → ∀ M : ℝ,1 ≤ M → M*R ≤ P →
        (M*R)^(s-1)*blockMomentSum k s P R M ≤ C*P^ε*(M*R)^s*(P/M)^lam/M^k := by
  obtain ⟨η,hη,C,hC,hbound⟩ := blockMomentSum_epsilon hadm hlam hε
  refine ⟨η,hη,C,hC,?_⟩
  intro P hP R hR hRP M hM hMR
  have hMR0 : 0 ≤ M*R := by positivity
  have hid : (M*R)^(s-1)*(M*R)=(M*R)^s := by rw [← pow_succ,Nat.sub_add_cancel hs]
  calc
    _ ≤ (M*R)^(s-1)*(C*P^ε*(M*R)*(P/M)^lam/M^k) :=
      mul_le_mul_of_nonneg_left (hbound P hP R hR hRP M hM hMR) (pow_nonneg hMR0 _)
    _ = C*P^ε*((M*R)^(s-1)*(M*R))*(P/M)^lam/M^k := by ring
    _ = _ := by rw [hid]

#print axioms weighted_blockMomentSum_epsilon
end Waring.RestrictedSmoothArcs
