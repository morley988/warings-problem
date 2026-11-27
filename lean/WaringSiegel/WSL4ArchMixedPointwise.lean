import WaringSiegel.WSL4ArchQuadraticAbs
import WaringSiegel.WSL4ArchEnlargedU
import WaringSiegel.WSL3PoissonMixedComplementS
import WaringSiegel.WSL3MomentCompactTrivial

/-! # Actual near-zero mixed-sixth integrand on the enlarged major arcs -/
noncomputable section
set_option maxHeartbeats 1800000
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def nearZeroMixedSIntegrand (H P M R : ℝ)
    (hH : H≠0) (hP : P≠0) (hM : M≠0) (hR : R≠0) : ArchimedeanTraceTorus K → ℂ :=
  compactMixedSIntegrand nearZeroSchwartz nearZeroSchwartz nearZeroSchwartz nearZeroSchwartz
    nearZeroSchwartz_majorant.2.1 nearZeroSchwartz_majorant.2.1
    nearZeroSchwartz_majorant.2.1 nearZeroSchwartz_majorant.2.1 H P M R hH hP hM hR

theorem nearZeroMixedSIntegrand_continuous (H P M R : ℝ)
    (hH : H≠0) (hP : P≠0) (hM : M≠0) (hR : R≠0) :
    Continuous (nearZeroMixedSIntegrand (K:=K) H P M R hH hP hM hR) := by
  unfold nearZeroMixedSIntegrand compactMixedSIntegrand
  apply Continuous.mul
  · apply continuous_finset_sum
    intro h hh
    exact (continuous_const.mul ((compactTraceWeylSum_continuous _ _ _ _ _).comp
      (traceTorusMul_continuous _))).mul ((compactTraceWeylSum_continuous _ _ _ _ _).comp
        (traceTorusMul_continuous _))
  · exact Complex.continuous_ofReal.comp
      (((compactTraceWeylSum_continuous _ _ _ _ _).comp (traceTorusMul_continuous _)).norm.pow 4)

theorem nearZeroMixedSIntegrand_trivial_sixth :
    ∃ C : ℝ, 0<C ∧ ∀ (H P M R : ℝ) (hH : H≠0) (hP : P≠0) (hM : 1≤M) (hR : R≠0),
      ∀ q : ArchimedeanTraceTorus K,
      ‖nearZeroMixedSIntegrand H P M R hH hP (by linarith) hR q‖ ≤
        C*M^finrank ℚ K *
          (∑ h ∈ (compactIntegerSupport nearZeroSchwartz nearZeroSchwartz_majorant.2.1 H hH).erase 0,
            ‖compactTraceWeylSum 2 nearZeroSchwartz nearZeroSchwartz_majorant.2.1 P hP
              (traceTorusMul (3*h) q)‖) *
          ‖nearZeroTraceCubicSum R hR (traceTorusMul 4 q)‖^4 := by
  obtain ⟨C,hC,hb⟩ := compactTraceWeylSum_trivial_bound
    (nearZeroSchwartz (K:=K)) nearZeroSchwartz_majorant.2.1
  refine ⟨C,hC,fun H P M R hH hP hM hR q => ?_⟩
  let U : Finset (𝓞 K) := (compactIntegerSupport nearZeroSchwartz nearZeroSchwartz_majorant.2.1 H hH).erase 0
  have hsum :
      ‖∑ h : U, nearZeroSchwartz (H⁻¹ • mixedEmbedding K ((h:𝓞 K):K)) *
        compactTraceWeylSum 2 nearZeroSchwartz nearZeroSchwartz_majorant.2.1 P hP
          (traceTorusMul (3*(h:𝓞 K)) q) *
        compactTraceWeylSum 6 nearZeroSchwartz nearZeroSchwartz_majorant.2.1 M (by linarith)
          (traceTorusMul ((h:𝓞 K)^3) q)‖ ≤
      C*M^finrank ℚ K * (∑ h ∈ U,
        ‖compactTraceWeylSum 2 nearZeroSchwartz nearZeroSchwartz_majorant.2.1 P hP
          (traceTorusMul (3*h) q)‖) := by
    apply (norm_sum_le _ _).trans
    rw [← Finset.sum_coe_sort U]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro h hh
    simp only [norm_mul]
    have hu := nearZeroSchwartz_majorant (K:=K) |>.2.2.2.2.1
    have hleft := mul_le_mul_of_nonneg_right (hu (H⁻¹ • mixedEmbedding K ((h:𝓞 K):K)))
      (norm_nonneg (compactTraceWeylSum 2 nearZeroSchwartz nearZeroSchwartz_majorant.2.1 P hP
        (traceTorusMul (3*(h:𝓞 K)) q)))
    have hright := hb M hM 6 (traceTorusMul ((h:𝓞 K)^3) q)
    rw [one_mul] at hleft
    exact (mul_le_mul hleft hright (norm_nonneg _)
      (norm_nonneg (compactTraceWeylSum 2 nearZeroSchwartz nearZeroSchwartz_majorant.2.1 P hP
        (traceTorusMul (3*(h:𝓞 K)) q)))).trans_eq (mul_comm _ _)
  unfold nearZeroMixedSIntegrand compactMixedSIntegrand
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) 4)]
  exact mul_le_mul_of_nonneg_right hsum (pow_nonneg (norm_nonneg _) 4)

theorem mixed_major_two_term_power (Z Q A : ℝ) (hZ : 0≤Z) (hQ : 0<Q) (hA : 0<A) :
    (Q*A)^(-(1/2):ℝ)*(Z*A^(-(1/3):ℝ)+Q*A^((2/3):ℝ))^4 ≤
      8*(Z^4*Q^(-(1/2):ℝ)*A^(-(11/6):ℝ)+Q^((7/2):ℝ)*A^((13/6):ℝ)) := by
  have hp := add_pow_le (mul_nonneg hZ (Real.rpow_nonneg hA.le (-(1/3):ℝ)))
    (mul_nonneg hQ.le (Real.rpow_nonneg hA.le ((2/3):ℝ))) 4
  norm_num only [show (4:ℕ)-1=3 by norm_num,show (2:ℝ)^3=8 by norm_num] at hp
  have hA1 : (A^(-(1/3):ℝ))^4=A^(-(4/3):ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hA.le]
    congr 1 <;> norm_num
  have hA2 : (A^((2/3):ℝ))^4=A^((8/3):ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hA.le]
    congr 1 <;> norm_num
  have h1 : A^(-(1/2):ℝ)*A^(-(4/3):ℝ)=A^(-(11/6):ℝ) := by
    rw [← Real.rpow_add hA]
    congr 1 <;> norm_num
  have h2 : A^(-(1/2):ℝ)*A^((8/3):ℝ)=A^((13/6):ℝ) := by
    rw [← Real.rpow_add hA]
    congr 1 <;> norm_num
  have hq : Q^(-(1/2):ℝ)*Q^4=Q^((7/2):ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hQ]
    congr 1 <;> norm_num
  have he : (Q*A)^(-(1/2):ℝ)*((Z*A^(-(1/3):ℝ))^4+(Q*A^((2/3):ℝ))^4) =
      Z^4*Q^(-(1/2):ℝ)*A^(-(11/6):ℝ)+Q^((7/2):ℝ)*A^((13/6):ℝ) := by
    rw [Real.mul_rpow hQ.le hA.le,mul_pow,mul_pow,hA1,hA2]
    calc
      _ = Z^4*Q^(-(1/2):ℝ)*(A^(-(1/2):ℝ)*A^(-(4/3):ℝ)) +
        (Q^(-(1/2):ℝ)*Q^4)*(A^(-(1/2):ℝ)*A^((8/3):ℝ)) := by ring
      _ = _ := by rw [h1,h2,hq]
  exact (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (mul_pos hQ hA).le _)).trans_eq
    (by rw [← he]; ring)

#print axioms nearZeroMixedSIntegrand_trivial_sixth
#print axioms mixed_major_two_term_power
end WaringSiegel.WSL4
