import Waring.SeedCompletionSparseWeightedCounts
import Mathlib.Algebra.Order.Chebyshev

/-! # Normalized finite Holder and height averaging for the actual counts -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseWeighted
open PolicyCompletionHolder

theorem integral_prod_le_of_power_bounds {s : ℕ} (hs : 0 < s)
    (g : Fin s → ℝ → ℝ) (hg : ∀ i, Continuous (g i))
    (hg0 : ∀ i x, 0 ≤ g i x) (T : Fin s → ℝ) (hT : ∀ i, 0 < T i)
    (D : ℝ) (hbound : ∀ i, (∫ x in (0 : ℝ)..1, (g i x)^s) ≤ D*(T i)^s) :
    (∫ x in (0 : ℝ)..1, ∏ i, g i x) ≤ D * ∏ i, T i := by
  let u : Fin s → ℝ → ℝ := fun i x => g i x / T i
  have hu (i : Fin s) : Continuous (u i) := (hg i).div_const _
  have hum (i : Fin s) : (∫ x in (0 : ℝ)..1, (u i x)^s) ≤ D := by
    simp only [u,div_pow]
    rw [intervalIntegral.integral_div]
    exact (div_le_iff₀ (pow_pos (hT i) _)).mpr (hbound i)
  have hm : (∫ x in (0 : ℝ)..1, ∏ i, u i x) ≤ D := by
    calc
      _ ≤ ∫ x in (0 : ℝ)..1, (s : ℝ)⁻¹ * ∑ i, (u i x)^s := by
        apply intervalIntegral.integral_mono_on zero_le_one
          ((continuous_finset_prod Finset.univ (fun i _ => hu i)).intervalIntegrable 0 1)
          ((continuous_const.mul (continuous_finset_sum Finset.univ
            (fun i _ => (hu i).pow s))).intervalIntegrable 0 1)
        intro x hx
        exact prod_le_average_pow hs (fun i => u i x)
          (fun i => div_nonneg (hg0 i x) (hT i).le)
      _ = (s : ℝ)⁻¹ * ∑ i, (∫ x in (0 : ℝ)..1, (u i x)^s) := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finset_sum
          (fun i _ => ((hu i).pow s).intervalIntegrable 0 1)]
      _ ≤ (s : ℝ)⁻¹ * ∑ _i : Fin s, D := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hum i))
        positivity
      _ = D := by
        have hsne : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
        simp [hsne]
  simp only [u,Finset.prod_div_distrib] at hm
  rw [intervalIntegral.integral_div] at hm
  exact (div_le_iff₀ (Finset.prod_pos (fun i _ => hT i))).mp hm

theorem integral_heightSum_pow_le {J s : ℕ} (hs : 0 < s)
    (H A : Fin s → Finset ℕ) (v : Fin s → ℕ → ℕ → Fin J → ℤ)
    (b : ℤ) (i : Fin s) (Hcap M D : ℝ) (hH : (H i).card ≤ Hcap)
    (hH0 : 0 ≤ Hcap) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hbound : ∀ h ∈ H i,
      frequencyEvenMoment (A i) (fun m => code b (v i h m)) s ≤ D*M^s) :
    (∫ x in (0 : ℝ)..1, (heightSum H A v b i x)^s) ≤ D*(Hcap*M)^s := by
  have hpoint (x : ℝ) : (heightSum H A v b i x)^s ≤
      ((H i).card : ℝ)^(s-1) *
        ∑ h ∈ H i, ‖frequencySum (A i) (fun m => code b (v i h m)) x‖^(2*s) := by
    have hh := pow_sum_le_card_mul_sum_pow
      (s := H i) (f := fun h => ‖frequencySum (A i) (fun m => code b (v i h m)) x‖^2)
      (fun h _ => sq_nonneg _) (s-1)
    simpa only [Nat.sub_add_cancel hs,← pow_mul,heightSum] using hh
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, ((H i).card : ℝ)^(s-1) *
        ∑ h ∈ H i, ‖frequencySum (A i) (fun m => code b (v i h m)) x‖^(2*s) := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (((continuous_heightSum H A v b i).pow s).intervalIntegrable 0 1)
        ((continuous_const.mul (continuous_finset_sum (H i) (fun h _ =>
          (continuous_frequencySum _ _).norm.pow (2*s)))).intervalIntegrable 0 1)
      exact fun x _ => hpoint x
    _ = ((H i).card : ℝ)^(s-1) * ∑ h ∈ H i,
        frequencyEvenMoment (A i) (fun m => code b (v i h m)) s := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_finset_sum
        (fun h _ => ((continuous_frequencySum _ _).norm.pow (2*s)).intervalIntegrable 0 1)]
      rfl
    _ ≤ ((H i).card : ℝ)^(s-1) * ∑ _h ∈ H i, D*M^s := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbound)
      positivity
    _ = ((H i).card : ℝ)^s * (D*M^s) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [← mul_assoc,← pow_succ,Nat.sub_add_cancel hs]
    _ ≤ Hcap^s * (D*M^s) := by gcongr
    _ = _ := by rw [mul_pow]; ring

theorem weightedCount_le_of_moments {J s : ℕ} (hs : 0 < s)
    (H A : Fin s → Finset ℕ) (v : Fin s → ℕ → ℕ → Fin J → ℤ)
    (b : ℤ) (Hcap M : Fin s → ℝ) (hH : ∀ i, (H i).card ≤ Hcap i)
    (hHpos : ∀ i, 0 < Hcap i) (hM : ∀ i, 0 < M i) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ h ∈ Fintype.piFinset H, ∀ d ∈ constraintVectors A (fun i => v i (h i)),
      code b d=0 ↔ d=0)
    (hbound : ∀ i, ∀ h ∈ H i,
      frequencyEvenMoment (A i) (fun m => code b (v i h m)) s ≤ D*(M i)^s) :
    (weightedCount H A v : ℝ) ≤ D * ∏ i, (Hcap i * M i) := by
  rw [weightedCount_eq_integral H A v b hb]
  exact integral_prod_le_of_power_bounds hs _ (continuous_heightSum H A v b)
    (heightSum_nonneg H A v b) _ (fun i => mul_pos (hHpos i) (hM i)) D
    (fun i => integral_heightSum_pow_le hs H A v b i (Hcap i) (M i) D
      (hH i) (hHpos i).le (hM i).le hD (hbound i))

#print axioms integral_prod_le_of_power_bounds
#print axioms weightedCount_le_of_moments
end Waring.SeedCompletionSparseWeighted
