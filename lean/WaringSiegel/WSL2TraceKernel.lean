import WaringSiegel.WSL2TraceMultiplication
import WaringSiegel.WSL2AnisotropicPacking

/-!
# WSL2: the actual finite multiplication kernel of the trace torus

The kernel is represented by a⁻¹D⁻¹ modulo D⁻¹. Its finiteness is proved
using the actual bounded fundamental domain and fractional-ideal packing.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def traceKernelFractionalIdeal (a : 𝓞 K) : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanSingleton (𝓞 K)⁰ ((a : K)⁻¹) * inverseDifferent K

theorem traceKernelFractionalIdeal_ne_zero (a : 𝓞 K) (ha : a ≠ 0) :
    traceKernelFractionalIdeal a ≠ 0 := by
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  exact mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero haK))
    inverseDifferent_ne_zero

theorem traceKernelFractionalIdeal_mem (a : 𝓞 K) (ha : a ≠ 0) (α : K) :
    α ∈ traceKernelFractionalIdeal a ↔ (a : K) * α ∈ inverseDifferent K := by
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  rw [traceKernelFractionalIdeal, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [← mul_assoc, mul_inv_cancel₀ haK, one_mul] using hz
  · intro h
    refine ⟨(a : K) * α, h, ?_⟩
    simp only [← mul_assoc, inv_mul_cancel₀ haK, one_mul]

theorem mixed_mul_mem_inverseDifferent_iff
    (a : 𝓞 K) (ha : a ≠ 0) (x : mixedSpace K) :
    mixedEmbedding K (a : K) * x ∈ archInverseDifferentLattice (K := K) ↔
      ∃ α : K, α ∈ traceKernelFractionalIdeal a ∧ mixedEmbedding K α = x := by
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  constructor
  · intro h
    obtain ⟨z, hz, he⟩ := (mem_archInverseDifferentLattice _).mp h
    refine ⟨(a : K)⁻¹ * z, (traceKernelFractionalIdeal_mem a ha _).mpr ?_, ?_⟩
    · simpa only [← mul_assoc, mul_inv_cancel₀ haK, one_mul] using hz
    · rw [map_mul, he, ← mul_assoc, ← map_mul, inv_mul_cancel₀ haK, map_one, one_mul]
  · rintro ⟨α, hα, rfl⟩
    rw [← map_mul]
    exact (mem_archInverseDifferentLattice _).mpr
      ⟨(a : K) * α, (traceKernelFractionalIdeal_mem a ha α).mp hα, rfl⟩

theorem traceTorusMul_kernel_mk_iff (a : 𝓞 K) (ha : a ≠ 0) (x : mixedSpace K) :
    Submodule.Quotient.mk x ∈ (traceTorusMul a).ker ↔
      ∃ α : K, α ∈ traceKernelFractionalIdeal a ∧ mixedEmbedding K α = x := by
  rw [AddMonoidHom.mem_ker, traceTorusMul_mk, Submodule.Quotient.mk_eq_zero]
  exact mixed_mul_mem_inverseDifferent_iff a ha x

/-- Every kernel point is a class of a genuine field element with the
expected inverse-different denominator. -/
theorem traceTorusMul_kernel_representative (a : 𝓞 K) (ha : a ≠ 0)
    {q : ArchimedeanTraceTorus K} (hq : q ∈ (traceTorusMul a).ker) :
    ∃ α : K, α ∈ traceKernelFractionalIdeal a ∧
      Submodule.Quotient.mk (mixedEmbedding K α) = q := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  obtain ⟨α, hα, he⟩ := (traceTorusMul_kernel_mk_iff a ha x).mp hq
  exact ⟨α, hα, by rw [he]; rfl⟩

/-- The actual multiplication kernel is finite. No finite-cover premise is
introduced; bounded fractional-ideal representatives supply the proof. -/
theorem traceTorusMul_kernel_finite (a : 𝓞 K) (ha : a ≠ 0) :
    ((traceTorusMul a).ker : Set (ArchimedeanTraceTorus K)).Finite := by
  let b := archimedeanTraceDualBasis (K := K)
  let R : ℝ := (∑ i, ‖b i‖) + 1
  have hR : 0 < R := by
    dsimp [R]
    exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) zero_lt_one
  let T := idealBox (traceKernelFractionalIdeal a) 0 0 (fun _ => R)
  have hT : T.Finite := idealBox_finite _ (traceKernelFractionalIdeal_ne_zero a ha)
    0 0 (fun _ => R) (fun _ => hR)
  apply (hT.image (fun α => (Submodule.Quotient.mk (mixedEmbedding K α) : ArchimedeanTraceTorus K))).subset
  intro q hq
  let y := ZSpan.quotientEquiv b q
  have hyq : Submodule.Quotient.mk (y : mixedSpace K) = q := by
    simpa only [ZSpan.quotientEquiv.symm_apply] using (ZSpan.quotientEquiv b).symm_apply_apply q
  have hyker : Submodule.Quotient.mk (y : mixedSpace K) ∈ (traceTorusMul a).ker := by rwa [hyq]
  obtain ⟨α, hα, he⟩ := (traceTorusMul_kernel_mk_iff a ha (y : mixedSpace K)).mp hyker
  refine ⟨α, ?_, by
    change Submodule.Quotient.mk (mixedEmbedding K α) = q
    rw [he, hyq]⟩
  have hynorm := ZSpan.norm_fract_le b (y : mixedSpace K)
  rw [ZSpan.fract_eq_self.mpr y.property] at hynorm
  refine ⟨by simpa only [sub_zero] using hα, ?_⟩
  intro w
  rw [sub_zero, he]
  exact (normAtPlace_le_mixed_norm _ w).trans (hynorm.trans (by dsimp [R]; linarith))

theorem traceTorusMul_kernel_finite_type (a : 𝓞 K) (ha : a ≠ 0) :
    Finite (traceTorusMul a).ker := by
  letI := (traceTorusMul_kernel_finite a ha).fintype
  infer_instance

end WaringSiegel
