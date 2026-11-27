import WaringSiegel.WSL2TraceResidueWeyl
import WaringSiegel.WSL2MomentHaarAverage

/-!
# Actual trace-Haar integral reduction in the mixed moment

The multiplier kernel preserves the small Weyl-sum factor. Exact Haar
averaging is followed by the proved residue-fiber Cauchy bound. Integrability
is established from the literal finite sums on the compact trace torus.
-/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField WaringSiegel.WSL2

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]
variable {α β : Type*} [Fintype α] [Fintype β]

theorem traceTorusCharacter_continuous (x : 𝓞 K) : Continuous (traceTorusCharacter x) := by
  unfold traceTorusCharacter latticeCharacter
  exact continuous_finset_prod _ (fun i _ => (fourier (integerCoordinates K x i)).continuous.comp
    ((continuous_apply i).comp (archimedeanTraceTorusContinuousAddEquiv (K := K)).continuous))

theorem traceWeylSum_continuous (k : ℕ) (nodes : α → 𝓞 K) (w : α → ℂ) :
    Continuous (traceWeylSum k nodes w) := by
  unfold traceWeylSum
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (traceTorusCharacter_continuous _))

theorem traceResidueWeylSum_continuous (a : 𝓞 K) (k : ℕ)
    (nodes : α → 𝓞 K) (w : α → ℂ) (r : PrincipalResidueRing a) :
    Continuous (traceResidueWeylSum a k nodes w r) := by
  unfold traceResidueWeylSum
  apply continuous_finset_sum
  intro i hi
  split_ifs
  · exact continuous_const.mul (traceTorusCharacter_continuous _)
  · exact continuous_const

theorem traceCoprimeWeylSum_continuous (a : 𝓞 K) (k : ℕ)
    (nodes : α → 𝓞 K) (w : α → ℂ) : Continuous (traceCoprimeWeylSum a k nodes w) := by
  unfold traceCoprimeWeylSum
  apply continuous_finset_sum
  intro i hi
  split_ifs
  · exact continuous_const.mul (traceTorusCharacter_continuous _)
  · exact continuous_const

theorem traceWeylSum_mul_kernel_invariant (a : 𝓞 K) (k : ℕ)
    (nodes : β → 𝓞 K) (w : β → ℂ) (η : (traceTorusMul a).ker)
    (θ : ArchimedeanTraceTorus K) :
    traceWeylSum k nodes w (traceTorusMul a (θ + η)) =
      traceWeylSum k nodes w (traceTorusMul a θ) := by
  rw [map_add, (AddMonoidHom.mem_ker.mp η.property), add_zero]

/-- The finite averaging step preserves the actual mixed integral exactly. -/
theorem trace_mixed_integral_kernel_average (a : 𝓞 K)
    [Fintype (traceTorusMul a).ker] (k : ℕ)
    (nodes : α → 𝓞 K) (w : α → ℂ) (small : β → 𝓞 K) (v : β → ℂ) :
    (∫ θ : ArchimedeanTraceTorus K,
      (𝔼 η : (traceTorusMul a).ker, ‖traceCoprimeWeylSum a k nodes w (θ + η)‖^2) *
      ‖traceWeylSum k small v (traceTorusMul a θ)‖^4 ∂traceHaar) =
    ∫ θ : ArchimedeanTraceTorus K, ‖traceCoprimeWeylSum a k nodes w θ‖^2 *
      ‖traceWeylSum k small v (traceTorusMul a θ)‖^4 ∂traceHaar := by
  refine integral_finite_translation_average_mul traceHaar
    (fun η : (traceTorusMul a).ker => (η : ArchimedeanTraceTorus K))
    (fun θ => ‖traceCoprimeWeylSum a k nodes w θ‖^2)
    (fun θ => ‖traceWeylSum k small v (traceTorusMul a θ)‖^4) ?_ ?_
  · apply Continuous.integrable_of_hasCompactSupport
    · exact ((traceCoprimeWeylSum_continuous a k nodes w).norm.pow 2).mul
        (((traceWeylSum_continuous k small v).comp (traceTorusMul_continuous a)).norm.pow 4)
    · exact HasCompactSupport.of_compactSpace _
  · intro η θ
    dsimp only
    rw [traceWeylSum_mul_kernel_invariant]

/-- The genuine mixed-moment congruence reduction, with its exact arithmetic
kernel multiplicity and no unproved pointwise Cauchy step. -/
theorem trace_mixed_moment_residue_reduction (a : 𝓞 K) (ha : a ≠ 0)
    [Fintype (PrincipalResidueRing a)] [Fintype (traceTorusMul a).ker]
    (k : ℕ) (nodes : α → 𝓞 K) (w : α → ℂ) (small : β → 𝓞 K) (v : β → ℂ) :
    (∫ θ : ArchimedeanTraceTorus K, ‖traceCoprimeWeylSum a k nodes w θ‖^2 *
      ‖traceWeylSum k small v (traceTorusMul a θ)‖^4 ∂traceHaar) ≤
      ((unitPowerKernel (PrincipalResidueRing a) k).card : ℝ) *
        ∫ θ : ArchimedeanTraceTorus K,
          (∑ r : (PrincipalResidueRing a)ˣ, ‖traceResidueWeylSum a k nodes w r θ‖^2) *
          ‖traceWeylSum k small v (traceTorusMul a θ)‖^4 ∂traceHaar := by
  let f : ArchimedeanTraceTorus K → ℝ := fun θ => ‖traceCoprimeWeylSum a k nodes w θ‖^2
  let g : ArchimedeanTraceTorus K → ℝ := fun θ => ‖traceWeylSum k small v (traceTorusMul a θ)‖^4
  let h : ArchimedeanTraceTorus K → ℝ := fun θ =>
    ∑ r : (PrincipalResidueRing a)ˣ, ‖traceResidueWeylSum a k nodes w r θ‖^2
  have hf : Continuous f := (traceCoprimeWeylSum_continuous a k nodes w).norm.pow 2
  have hg : Continuous g :=
    ((traceWeylSum_continuous k small v).comp (traceTorusMul_continuous a)).norm.pow 4
  have hh : Continuous h := continuous_finset_sum _
    (fun r _ => (traceResidueWeylSum_continuous a k nodes w r).norm.pow 2)
  have hfg : Integrable (fun θ => f θ * g θ) traceHaar :=
    (hf.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hinv : ∀ (η : (traceTorusMul a).ker) θ, g (θ + η) = g θ := by
    intro η θ
    dsimp [g]
    rw [traceWeylSum_mul_kernel_invariant]
  let M : ℝ := (unitPowerKernel (PrincipalResidueRing a) k).card
  change (∫ θ, f θ * g θ ∂traceHaar) ≤ M * ∫ θ, h θ * g θ ∂traceHaar
  calc
    _ = ∫ θ : ArchimedeanTraceTorus K, (𝔼 η : (traceTorusMul a).ker, f (θ + η)) * g θ ∂traceHaar :=
      (integral_finite_translation_average_mul traceHaar
        (fun η : (traceTorusMul a).ker => (η : ArchimedeanTraceTorus K)) f g hfg hinv).symm
    _ ≤ ∫ θ, M * (h θ * g θ) ∂traceHaar := by
      apply integral_mono
      · exact integrable_finite_translation_average_mul traceHaar
          (fun η : (traceTorusMul a).ker => (η : ArchimedeanTraceTorus K)) f g hfg hinv
      · exact (continuous_const.mul (hh.mul hg)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro θ
        have hbound : (𝔼 η : (traceTorusMul a).ker, f (θ + η)) ≤ M * h θ :=
          traceCoprimeWeylSum_kernel_average_le a ha k nodes w θ
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hbound
          (pow_nonneg (norm_nonneg _) 4)
    _ = _ := integral_const_mul M (fun θ => h θ * g θ)

end WaringSiegel
