import WaringSiegel.WSL3AuxiliaryQuotientUnits
import WaringSiegel.WSL4MixedKernelToCount

/-! # The cubic mixed moment uses the original coprimality mask -/
noncomputable section
open NumberField
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
variable {K : Type*} [Field K] [NumberField K]

theorem principal_power_quotient_isUnit_iff (a x : 𝓞 K) (n : ℕ) (hn : 1≤n) :
    IsUnit (Ideal.Quotient.mk (Ideal.span ({a^n}:Set (𝓞 K))) x) ↔
      IsUnit (Ideal.Quotient.mk (Ideal.span ({a}:Set (𝓞 K))) x) := by
  let I := Ideal.span ({a^n}:Set (𝓞 K))
  let J := Ideal.span ({a}:Set (𝓞 K))
  have hJI : J^n=I := Ideal.span_singleton_pow a n
  have hIJ : I≤J := by
    rw [← hJI]
    simpa only [pow_one] using (Ideal.pow_le_pow_right (I:=J) hn)
  have hh := quotient_factor_isUnit_iff_of_power_le I J hIJ n hJI.le
    (Ideal.Quotient.mk I x)
  simpa only [Ideal.Quotient.factor_mk] using hh.symm

theorem traceCoprimeWeylSum_power_modulus {α : Type*} [Fintype α]
    (a : 𝓞 K) (n : ℕ) (hn : 1≤n) (k : ℕ) (x : α→𝓞 K) (w : α→ℂ)
    (q : ArchimedeanTraceTorus K) :
    traceCoprimeWeylSum (a^n) k x w q = traceCoprimeWeylSum a k x w q := by
  simp only [traceCoprimeWeylSum,principal_power_quotient_isUnit_iff a _ n hn]

#print axioms principal_power_quotient_isUnit_iff
#print axioms traceCoprimeWeylSum_power_modulus
end WaringSiegel.WSL4Local
