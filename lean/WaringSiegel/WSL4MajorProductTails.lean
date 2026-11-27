import WaringSiegel.WSL4MajorScaling
import WaringSiegel.WSL3UnitFrequencyTails

/-! # Target-uniform tails for the exact product-frequency truncation

The conductor arc truncates the singular integral by productArcWeight,
rather than a ball.  Its complement is controlled by genuine moments of
the paired smooth root integral, with every inverse power of the cutoff.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory MeasureTheory.Measure NumberField NumberField.InfinitePlace
  NumberField.mixedEmbedding Module WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators Pointwise ENNReal
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem productFrequencyRegion_measurableSet (Q : ℝ) :
    MeasurableSet (productFrequencyRegion (K := K) Q) :=
  (isClosed_le (productArcWeight_continuous 1) continuous_const).measurableSet

theorem productArcWeight_le_radial (β : mixedSpace K) :
    productArcWeight 1 β ≤ (1+‖β‖)^(finrank ℚ K) := by
  calc
    _ ≤ ∏ w : InfinitePlace K, (1+‖β‖)^(mult w) := by
      apply Finset.prod_le_prod
      · intro w hw
        exact pow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
      · intro w hw
        apply pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _))
        simp only [one_mul]
        exact max_le (by linarith [norm_nonneg β])
          ((normAtPlace_le_mixed_norm β w).trans (by linarith))
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum,InfinitePlace.sum_mult_eq]

theorem pairedSmoothRootIntegral_continuous (a : ℝ) (ha : 0≤a) (k : ℕ)
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) :
    Continuous (pairedWeightedRootIntegral a k (smoothRootWeight (K := K) ρ R)) := by
  have he : pairedWeightedRootIntegral a k (smoothRootWeight (K := K) ρ R) =
      fun β => a • weightedRootIntegral k (smoothRootWeight ρ R) β :=
    funext (pairedWeightedRootIntegral_eq a ha k _)
  rw [he]
  exact continuous_const.smul (weightedRootIntegral_continuous k ρ R hρ hR)

theorem pairedSmooth_positive_phase_integrable (a : ℝ) (ha : 0<a) (k s : ℕ)
    (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (b : mixedSpace K) :
    Integrable (fun β : mixedSpace K => archimedeanTraceCharacter (-β) b *
      pairedWeightedRootIntegral a k (smoothRootWeight ρ R) β^(s+1))
      (archimedeanDualMeasure a) := by
  simp_rw [pairedWeightedRootIntegral_eq a ha.le,smul_pow,mul_smul_comm]
  rw [archimedeanDualMeasure]
  exact ((weightedRootIntegral_positive_phase_integrable k s hk ρ R hρ hR b).smul _).smul_measure
    ENNReal.ofReal_ne_top

theorem pairedSmooth_radial_moment_integrable (a : ℝ) (ha : 0<a) (k s : ℕ)
    (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (N : ℕ) :
    Integrable (fun β : mixedSpace K => (1+‖β‖)^N *
      ‖pairedWeightedRootIntegral a k (smoothRootWeight ρ R) β^(s+1)‖)
      (archimedeanDualMeasure a) := by
  simp_rw [pairedWeightedRootIntegral_eq a ha.le,smul_pow,_root_.norm_smul,
    Real.norm_of_nonneg (pow_nonneg ha.le (s+1))]
  rw [archimedeanDualMeasure]
  have h := ((weightedRootIntegral_power_moment_integrable (K := K) k s hk ρ R hρ hR N).const_mul
    (a^(s+1))).smul_measure (c := ENNReal.ofReal (((4:ℝ)^nrComplexPlaces K)/a))
      ENNReal.ofReal_ne_top
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

theorem pairedSmooth_product_moment_integrable (a : ℝ) (ha : 0<a) (k s : ℕ)
    (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (N : ℕ) :
    Integrable (fun β : mixedSpace K => productArcWeight 1 β^N *
      ‖pairedWeightedRootIntegral a k (smoothRootWeight ρ R) β^(s+1)‖)
      (archimedeanDualMeasure a) := by
  apply (pairedSmooth_radial_moment_integrable a ha k s hk ρ R hρ hR
    (finrank ℚ K*N)).mono'
  · exact (((productArcWeight_continuous 1).pow N).mul
      (((pairedSmoothRootIntegral_continuous a ha.le k ρ R hρ hR).pow (s+1)).norm)).aestronglyMeasurable
  · filter_upwards with β
    rw [Real.norm_of_nonneg (mul_nonneg
      (pow_nonneg (productArcWeight_pos 1 β).le N) (norm_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [pow_mul] using
      pow_le_pow_left₀ (productArcWeight_pos 1 β).le (productArcWeight_le_radial β) N

theorem pairedSmooth_product_frequency_tail (a : ℝ) (ha : 0<a) (k s : ℕ)
    (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ Q : ℝ, 0<Q →
      (∫ β in (productFrequencyRegion (K := K) Q)ᶜ,
        ‖pairedWeightedRootIntegral a k (smoothRootWeight ρ R) β^(s+1)‖
          ∂archimedeanDualMeasure a) ≤ C/Q^N := by
  let F : mixedSpace K → ℝ := fun β => productArcWeight 1 β^N *
    ‖pairedWeightedRootIntegral a k (smoothRootWeight ρ R) β^(s+1)‖
  have hi : Integrable F (archimedeanDualMeasure a) :=
    pairedSmooth_product_moment_integrable a ha k s hk ρ R hρ hR N
  have hF : ∀ β, 0≤F β := fun β => by
    exact mul_nonneg (pow_nonneg (productArcWeight_pos 1 β).le _) (norm_nonneg _)
  have hn : Integrable (fun β : mixedSpace K =>
      ‖pairedWeightedRootIntegral a k (smoothRootWeight ρ R) β^(s+1)‖)
      (archimedeanDualMeasure a) := by
    simpa only [pow_zero,one_mul] using
      pairedSmooth_product_moment_integrable a ha k s hk ρ R hρ hR 0
  have hIntegral : 0≤∫ β,F β ∂archimedeanDualMeasure a := integral_nonneg hF
  refine ⟨(∫ β,F β ∂archimedeanDualMeasure a)+1,by linarith,?_⟩
  intro Q hQ
  apply (le_div_iff₀ (pow_pos hQ N)).mpr
  have hbound : (∫ β in (productFrequencyRegion (K := K) Q)ᶜ,
      Q^N*‖pairedWeightedRootIntegral a k (smoothRootWeight ρ R) β^(s+1)‖
        ∂archimedeanDualMeasure a) ≤
      ∫ β in (productFrequencyRegion (K := K) Q)ᶜ,F β ∂archimedeanDualMeasure a := by
    apply setIntegral_mono_on (hn.const_mul _).integrableOn hi.integrableOn
      (productFrequencyRegion_measurableSet Q).compl
    intro β hβ
    have hβ' : Q ≤ productArcWeight 1 β :=
      (lt_of_not_ge (show ¬productArcWeight 1 β≤Q from hβ)).le
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hQ.le hβ' N) (norm_nonneg _)
  rw [integral_const_mul] at hbound
  have htotal := setIntegral_le_integral hi (Filter.Eventually.of_forall hF)
    (s := (productFrequencyRegion (K := K) Q)ᶜ)
  nlinarith

theorem productSingularIntegral_truncation
    (k s : ℕ) (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ Q : ℝ, 0<Q → ∀ b : mixedSpace K,
      ‖pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
          (smoothRootWeight ρ R) b - productSingularIntegral k (s+1) ρ R Q b‖ ≤ C/Q^N := by
  obtain ⟨C,hC,hb⟩ := pairedSmooth_product_frequency_tail (K := K)
    (integerLatticeSourceScale K) integerLatticeSourceScale_pos k s hk ρ R hρ hR N
  refine ⟨C,hC,fun Q hQ b => ?_⟩
  rw [pairedWeightedSingularIntegral,productSingularIntegral,
    ← setIntegral_compl (productFrequencyRegion_measurableSet Q)
      (pairedSmooth_positive_phase_integrable _ integerLatticeSourceScale_pos k s hk ρ R hρ hR b)]
  apply (norm_integral_le_integral_norm _).trans
  simpa only [norm_mul,archimedeanTraceCharacter_norm,one_mul] using hb Q hQ

#print axioms pairedSmooth_product_moment_integrable
#print axioms productSingularIntegral_truncation
end WaringSiegel.WSL4
