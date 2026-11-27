import WaringSiegel.WSL2TraceKernelCharacters

/-!
# WSL2: actual residue-class characters induced by the trace kernel

This identifies finite-kernel averaging with congruence orthogonality on the
actual quotient ring of integers modulo the principal ideal (a).
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def traceFrequencyAddChar (q : ArchimedeanTraceTorus K) : AddChar (𝓞 K) ℂ where
  toFun x := traceTorusCharacter x q
  map_zero_eq_one' := by simp [traceTorusCharacter, latticeCharacter]
  map_add_eq_mul' x y := by
    simp only [traceTorusCharacter, map_add, latticeCharacter_add]

abbrev PrincipalResidueRing (a : 𝓞 K) := 𝓞 K ⧸ Ideal.span ({a} : Set (𝓞 K))

theorem principalResidueRing_finite (a : 𝓞 K) (ha : a ≠ 0) :
    Finite (PrincipalResidueRing a) :=
  Ideal.finiteQuotientOfFreeOfNeBot (Ideal.span {a})
    (mt Ideal.span_singleton_eq_bot.mp ha)

theorem principalIdeal_le_traceFrequency_kernel (a : 𝓞 K)
    (q : (traceTorusMul a).ker) :
    (Ideal.span ({a} : Set (𝓞 K))).toAddSubgroup ≤
      (traceFrequencyAddChar (q : ArchimedeanTraceTorus K)).toAddMonoidHom.ker := by
  intro x hx
  change traceTorusCharacter x q = 1
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
  rw [traceTorusCharacter_mul, (AddMonoidHom.mem_ker.mp q.property),
    traceTorusCharacter_zero]

def traceResidueAddChar (a : 𝓞 K) (q : (traceTorusMul a).ker) :
    AddChar (PrincipalResidueRing a) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift
    (Ideal.span ({a} : Set (𝓞 K))).toAddSubgroup
    (traceFrequencyAddChar (q : ArchimedeanTraceTorus K)).toAddMonoidHom
    (principalIdeal_le_traceFrequency_kernel a q))

theorem traceResidueAddChar_mk (a x : 𝓞 K) (q : (traceTorusMul a).ker) :
    traceResidueAddChar a q (Ideal.Quotient.mk (Ideal.span ({a} : Set (𝓞 K))) x) =
      traceTorusCharacter x q := rfl

/-- Orthogonality for the actual trace-kernel family on the actual quotient ring. -/
theorem traceResidueAddChar_average (a : 𝓞 K) (ha : a ≠ 0)
    [Fintype (traceTorusMul a).ker] (b : PrincipalResidueRing a) :
    (𝔼 q : (traceTorusMul a).ker, traceResidueAddChar a q b) =
      if b = 0 then 1 else 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [traceResidueAddChar_mk, traceKernel_character_average a ha x,
    Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

end WaringSiegel
