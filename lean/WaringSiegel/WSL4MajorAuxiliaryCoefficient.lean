import WaringSiegel.WSL4MajorAuxiliarySources

/-! # The literal auxiliary coefficient on an arbitrary major cutoff -/
noncomputable section
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def auxiliaryMajorCoefficient (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) (L : ℝ) (target : 𝓞 K) : ℂ :=
  ∫ q in traceMajorArcUnion (P^3) L,
    auxiliaryTraceIntegrand ρ R hρ hR P hP p hp target q ∂traceHaar

end WaringSiegel.WSL4
