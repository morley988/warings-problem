import WaringSiegel.WSL2TraceKernel
import WaringSiegel.WSL2TraceMoments
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality

/-!
# WSL2: exact characters of the actual trace-torus multiplication kernel

The annihilator is proved to be the principal ideal (a), using the actual
trace-dual basis. Thus averaging over the finite kernel imposes the genuine
congruence modulo a; the orthogonality relation is not an analytic premise.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem traceTorusCharacter_zero (x : 𝓞 K) :
    traceTorusCharacter x (0 : ArchimedeanTraceTorus K) = 1 := by
  simp [traceTorusCharacter, latticeCharacter, fourier_eval_zero]

theorem traceTorusCharacter_add (x : 𝓞 K) (p q : ArchimedeanTraceTorus K) :
    traceTorusCharacter x (p + q) = traceTorusCharacter x p * traceTorusCharacter x q := by
  simp only [traceTorusCharacter, map_add, latticeCharacter, Pi.add_apply,
    fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul,
    Finset.prod_mul_distrib]

def traceTorusAddChar (x : 𝓞 K) : AddChar (ArchimedeanTraceTorus K) ℂ where
  toFun := traceTorusCharacter x
  map_zero_eq_one' := traceTorusCharacter_zero x
  map_add_eq_mul' := traceTorusCharacter_add x

theorem traceTorusCharacter_mul (a x : 𝓞 K) (q : ArchimedeanTraceTorus K) :
    traceTorusCharacter (a * x) q = traceTorusCharacter x (traceTorusMul a q) := by
  obtain ⟨z, rfl⟩ := Quotient.exists_rep q
  change traceTorusCharacter (a * x) (Submodule.Quotient.mk z) =
    traceTorusCharacter x (traceTorusMul a (Submodule.Quotient.mk z))
  simp only [traceTorusMul_mk, traceTorusCharacter_mk, RingOfIntegers.coe_eq_algebraMap,
    map_mul, mul_assoc, mul_left_comm]

theorem traceExp_eq_one_iff_integer (t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) = 1 ↔
      ∃ n : ℤ, (n : ℝ) = t := by
  have h : fourier (1 : ℤ) (t : AddCircle (1 : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) := by
    rw [fourier_coe_apply]
    norm_num
  rw [← h, fourier_one]
  constructor
  · intro ht
    have hc : AddCircle.toCircle (t : AddCircle (1 : ℝ)) =
        AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      apply Subtype.ext
      simpa using ht
    have hz := AddCircle.injective_toCircle one_ne_zero hc
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    exact ⟨n, by simpa only [zsmul_eq_mul, mul_one] using hn⟩
  · rintro ⟨n, rfl⟩
    have hz : ((n : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simp⟩
    simp [hz]

/-- A character vanishes on the actual finite kernel precisely when its
integer frequency belongs to the principal ideal (a). -/
theorem traceTorusMul_kernel_annihilator (a : 𝓞 K) (ha : a ≠ 0) (x : 𝓞 K) :
    (∀ q : (traceTorusMul a).ker, traceTorusCharacter x q = 1) ↔ a ∣ x := by
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha
  constructor
  · intro h
    have hcoords : ∀ i, ∃ n : ℤ,
        (n : ℚ) = (NumberField.integralBasis K).repr ((x : K) / a) i := by
      intro i
      let α : K := (a : K)⁻¹ * integralTraceDualBasis K i
      have hα : α ∈ traceKernelFractionalIdeal a := by
        apply (traceKernelFractionalIdeal_mem a ha α).mpr
        simpa only [α, ← mul_assoc, mul_inv_cancel₀ haK, one_mul] using
          integralTraceDualBasis_mem_inverseDifferent K i
      have hq : Submodule.Quotient.mk (mixedEmbedding K α) ∈ (traceTorusMul a).ker :=
        (traceTorusMul_kernel_mk_iff a ha _).mpr ⟨α, hα, rfl⟩
      have he := h ⟨Submodule.Quotient.mk (mixedEmbedding K α), hq⟩
      change traceTorusCharacter x (Submodule.Quotient.mk (mixedEmbedding K α)) = 1 at he
      rw [traceTorusCharacter_mk, ← map_mul, archimedeanTrace_field] at he
      obtain ⟨n, hn⟩ := (traceExp_eq_one_iff_integer _).mp he
      refine ⟨n, ?_⟩
      have hrepr := rational_basis_repr_eq_trace K (NumberField.integralBasis K)
        ((x : K) / a) i
      rw [hrepr]
      change (n : ℚ) = Algebra.trace ℚ K (((x : K) / a) * integralTraceDualBasis K i)
      have hmul : (x : K) * α = ((x : K) / a) * integralTraceDualBasis K i := by
        dsimp [α]
        rw [div_eq_mul_inv, mul_assoc]
      rw [hmul] at hn
      exact_mod_cast hn
    have hint : (x : K) / a ∈ (algebraMap (𝓞 K) K).range := by
      apply (NumberField.mem_span_integralBasis K).mp
      rw [(NumberField.integralBasis K).mem_span_iff_repr_mem ℤ]
      exact hcoords
    obtain ⟨y, hy⟩ := hint
    change (y : K) = (x : K) / a at hy
    refine ⟨y, ?_⟩
    apply RingOfIntegers.ext
    change (x : K) = (a : K) * y
    rw [hy]
    field_simp
  · rintro ⟨y, rfl⟩ q
    rw [traceTorusCharacter_mul, (AddMonoidHom.mem_ker.mp q.property),
      traceTorusCharacter_zero]

def traceKernelAddChar (a x : 𝓞 K) : AddChar (traceTorusMul a).ker ℂ :=
  (traceTorusAddChar x).compAddMonoidHom (traceTorusMul a).ker.subtype

theorem traceKernelAddChar_eq_zero_iff (a : 𝓞 K) (ha : a ≠ 0) (x : 𝓞 K) :
    traceKernelAddChar a x = 0 ↔ a ∣ x := by
  rw [← traceTorusMul_kernel_annihilator a ha x]
  constructor
  · intro h q
    have hq := congrArg (fun χ : AddChar (traceTorusMul a).ker ℂ => χ q) h
    exact hq
  · intro h
    ext q
    exact h q

/-- Exact congruence orthogonality on the actual multiplication kernel. -/
theorem traceKernel_character_average (a : 𝓞 K) (ha : a ≠ 0) (x : 𝓞 K)
    [Fintype (traceTorusMul a).ker] :
    (𝔼 q : (traceTorusMul a).ker, traceTorusCharacter x q) = if a ∣ x then 1 else 0 := by
  change (𝔼 q, traceKernelAddChar a x q) = _
  simp only [AddChar.expect_eq_ite, traceKernelAddChar_eq_zero_iff a ha x]

end WaringSiegel
