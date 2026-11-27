import WaringSiegel.TraceCoordinates
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The actual inverse different in trace-dual coordinates

The integer span of the constructed trace-dual basis is the inverse of
mathlib's actual different ideal.  Equivalently, the field-valued points sent
to zero in the coordinate torus are precisely the inverse different.
This is an algebraic statement; no identification of archimedean topologies
or Haar measures is asserted here.
-/

noncomputable section
open scoped NumberField BigOperators nonZeroDivisors

namespace WaringSiegel

variable (K : Type*) [Field K] [NumberField K]

/-- The inverse of the actual different ideal of `𝓞 K / ℤ`. -/
def inverseDifferent : FractionalIdeal (𝓞 K)⁰ K :=
  (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹

/-- Compatibility with mathlib's trace-dual fractional ideal. -/
theorem inverseDifferent_eq_dual :
    inverseDifferent K = FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [inverseDifferent, coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]

/-- The trace-dual basis is an integral lattice basis for the actual inverse different. -/
theorem span_integralTraceDualBasis :
    Submodule.span ℤ (Set.range (integralTraceDualBasis K)) =
      (inverseDifferent K : Submodule (𝓞 K) K).restrictScalars ℤ := by
  classical
  have hb : Submodule.span ℤ (Set.range (NumberField.integralBasis K)) =
      (1 : Submodule (𝓞 K) K).restrictScalars ℤ := by
    ext x
    simpa only [Submodule.restrictScalars_mem, Submodule.mem_one, RingHom.mem_range] using
      NumberField.mem_span_integralBasis K (x := x)
  rw [inverseDifferent_eq_dual, FractionalIdeal.coe_dual_one]
  change Submodule.span ℤ (Set.range (integralTraceDualBasis K)) =
    (Algebra.traceForm ℚ K).dualSubmodule ((1 : Submodule (𝓞 K) K).restrictScalars ℤ)
  rw [← hb]
  exact ((Algebra.traceForm ℚ K).dualSubmodule_span_of_basis
    (traceForm_nondegenerate ℚ K) (NumberField.integralBasis K)).symm

/-- Membership in the inverse different is exactly integrality of all trace-dual coordinates. -/
theorem mem_inverseDifferent_iff_dualCoordinates (α : K) :
    α ∈ inverseDifferent K ↔ ∀ i, ∃ n : ℤ,
      (n : ℚ) = (integralTraceDualBasis K).repr α i := by
  change α ∈ (inverseDifferent K : Submodule (𝓞 K) K).restrictScalars ℤ ↔ _
  rw [← span_integralTraceDualBasis, (integralTraceDualBasis K).mem_span_iff_repr_mem ℤ]
  rfl

/-- In particular, each trace-dual basis vector lies in the inverse different. -/
theorem integralTraceDualBasis_mem_inverseDifferent (i : NumberFieldCoordinateIndex K) :
    integralTraceDualBasis K i ∈ inverseDifferent K := by
  change integralTraceDualBasis K i ∈
    (inverseDifferent K : Submodule (𝓞 K) K).restrictScalars ℤ
  rw [← span_integralTraceDualBasis]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- The inverse different is precisely the lattice of integral trace pairings. -/
theorem mem_inverseDifferent_iff_trace_integral (α : K) :
    α ∈ inverseDifferent K ↔ ∀ x : 𝓞 K, ∃ n : ℤ,
      (n : ℚ) = Algebra.trace ℚ K ((x : K) * α) := by
  rw [inverseDifferent_eq_dual,
    FractionalIdeal.mem_dual (A := ℤ) (K := ℚ)
      (I := (1 : FractionalIdeal (𝓞 K)⁰ K)) one_ne_zero]
  constructor
  · intro h x
    have hx := h (x : K) (FractionalIdeal.coe_mem_one (𝓞 K)⁰ x)
    simpa only [Algebra.traceForm_apply, mul_comm α (x : K), RingHom.mem_range] using hx
  · intro h y hy
    obtain ⟨x, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hy
    simpa only [Algebra.traceForm_apply, mul_comm α (x : K), RingHom.mem_range] using h x

/-- The coordinate-torus map has exactly the inverse different as its kernel. -/
theorem traceTorusPoint_eq_zero_iff (α : K) :
    traceTorusPoint K α = 0 ↔ α ∈ inverseDifferent K := by
  rw [mem_inverseDifferent_iff_dualCoordinates]
  constructor
  · intro h i
    have hi : (((integralTraceDualBasis K).repr α i : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      congrFun h i
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
    refine ⟨n, ?_⟩
    have hn' : (n : ℝ) = ((integralTraceDualBasis K).repr α i : ℝ) := by
      simpa only [zsmul_eq_mul, mul_one] using hn
    exact_mod_cast hn'
  · intro h
    funext i
    obtain ⟨n, hn⟩ := h i
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    refine ⟨n, ?_⟩
    change n • (1 : ℝ) = ((integralTraceDualBasis K).repr α i : ℝ)
    rw [← hn]
    simp

/-- The trace character is trivial on the actual inverse different. -/
theorem latticeCharacter_eq_one_of_mem_inverseDifferent (x : 𝓞 K) {α : K}
    (hα : α ∈ inverseDifferent K) :
    latticeCharacter (integerCoordinates K x) (traceTorusPoint K α) = 1 := by
  rw [(traceTorusPoint_eq_zero_iff K α).mpr hα]
  simp [latticeCharacter]

end WaringSiegel

#print axioms WaringSiegel.span_integralTraceDualBasis
#print axioms WaringSiegel.traceTorusPoint_eq_zero_iff
