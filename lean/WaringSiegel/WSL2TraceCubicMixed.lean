import WaringSiegel.WSL2TraceMixedReduction
import WaringSiegel.WSL2LocalGlobalKernel

/-!
# WSL2: the actual cubic mixed-moment reduction with epsilon multiplicity

This combines genuine trace-torus kernel averaging with the proved global
cubing-kernel estimate on actual residue-ring units. The arithmetic epsilon
constant is chosen before the modulus, the node sets, and all weights.
The conclusion is an integral inequality, not an unaveraged pointwise bound.
-/

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField WaringSiegel.WSL2

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem unitPowerKernel_cube_card (R : Type*) [CommRing R] [Fintype R] :
    (unitPowerKernel R 3).card = cubeUnitKernelCard R := by
  simp only [unitPowerKernel, powerKernel, cubeUnitKernelCard,
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext u
  simp

theorem trace_cubic_mixed_moment_epsilon_reduction {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {α β : Type*} [Fintype α] [Fintype β]
        (a : 𝓞 K) (ha : a ≠ 0)
        [Fintype (PrincipalResidueRing a)] [Fintype (traceTorusMul a).ker]
        (nodes : α → 𝓞 K) (w : α → ℂ) (small : β → 𝓞 K) (v : β → ℂ),
      (∫ θ : ArchimedeanTraceTorus K, ‖traceCoprimeWeylSum a 3 nodes w θ‖^2 *
        ‖traceWeylSum 3 small v (traceTorusMul a θ)‖^4 ∂traceHaar) ≤
      (C*(Ideal.absNorm (Ideal.span ({a} : Set (𝓞 K))) : ℝ)^ε) *
        ∫ θ : ArchimedeanTraceTorus K,
          (∑ r : (PrincipalResidueRing a)ˣ, ‖traceResidueWeylSum a 3 nodes w r θ‖^2) *
          ‖traceWeylSum 3 small v (traceTorusMul a θ)‖^4 ∂traceHaar := by
  obtain ⟨C, hC, hbound⟩ := ideal_cube_unit_kernel_epsilon_bound (K := K) hε
  refine ⟨C, hC, ?_⟩
  intro α β _ _ a ha _ _ nodes w small v
  have hI : Ideal.span ({a} : Set (𝓞 K)) ≠ 0 := mt Ideal.span_singleton_eq_bot.mp ha
  have hkernel := hbound (Ideal.span ({a} : Set (𝓞 K))) hI
  have hnonneg : 0 ≤ ∫ θ : ArchimedeanTraceTorus K,
      (∑ r : (PrincipalResidueRing a)ˣ, ‖traceResidueWeylSum a 3 nodes w r θ‖^2) *
        ‖traceWeylSum 3 small v (traceTorusMul a θ)‖^4 ∂traceHaar := by
    apply integral_nonneg
    intro θ
    exact mul_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (pow_nonneg (norm_nonneg _) 4)
  have hr := trace_mixed_moment_residue_reduction a ha 3 nodes w small v
  rw [unitPowerKernel_cube_card] at hr
  exact hr.trans (mul_le_mul_of_nonneg_right hkernel hnonneg)

end WaringSiegel
