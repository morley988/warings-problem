import WaringSiegel.WSL4ArchAuxiliarySources
import WaringSiegel.WSL4MajorCharacters
import WaringSiegel.WSL3AuxiliaryRationalCenters

/-! # The literal prime-masked four-by-four trace integrand -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField Classical BigOperators SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson WSL4Local
variable {K : Type*} [Field K] [NumberField K]

def auxiliaryTraceProduct (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) (q : ArchimedeanTraceTorus K) : ℂ :=
  compactCoprimeTraceCubicSum (smoothWeightSchwartz ρ R hρ hR) P p q 0 ^4 *
    smoothTraceSource 3 ρ R hρ hR (P/(p:ℝ)) (div_pos hP (Nat.cast_pos.mpr hp)).ne'
      (traceTorusMul ((p:𝓞 K)^3) q) ^4

def auxiliaryTraceIntegrand (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) (target : 𝓞 K)
    (q : ArchimedeanTraceTorus K) : ℂ :=
  auxiliaryTraceProduct ρ R hρ hR P hP p hp q * traceTorusCharacter (-target) q

theorem auxiliaryTraceProduct_continuous (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) :
    Continuous (auxiliaryTraceProduct (K := K) ρ R hρ hR P hP p hp) := by
  have hf : Continuous (fun q : ArchimedeanTraceTorus K =>
      compactCoprimeTraceCubicSum (smoothWeightSchwartz ρ R hρ hR) P p q 0) := by
    simp_rw [compactCoprimeTraceCubicSum_eq_finite _
      (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) P hP.ne' p,finiteLinearTraceSum]
    apply continuous_finset_sum
    intro x hx
    exact (continuous_const.mul (traceTorusCharacter_continuous (x^3))).mul continuous_const
  exact (hf.pow 4).mul
    (((smoothTraceSource_continuous 3 ρ R hρ hR _ _).comp
      (traceTorusMul_continuous ((p:𝓞 K)^3))).pow 4)

theorem auxiliaryTraceIntegrand_continuous (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) (target : 𝓞 K) :
    Continuous (auxiliaryTraceIntegrand ρ R hρ hR P hP p hp target) :=
  (auxiliaryTraceProduct_continuous ρ R hρ hR P hP p hp).mul
    (traceTorusCharacter_continuous _)

theorem auxiliaryTraceIntegrand_norm (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) (target : 𝓞 K)
    (q : ArchimedeanTraceTorus K) :
    ‖auxiliaryTraceIntegrand ρ R hρ hR P hP p hp target q‖ =
      ‖compactCoprimeTraceCubicSum (smoothWeightSchwartz ρ R hρ hR) P p q 0‖^4 *
      ‖smoothTraceSource 3 ρ R hρ hR (P/(p:ℝ)) (div_pos hP (Nat.cast_pos.mpr hp)).ne'
        (traceTorusMul ((p:𝓞 K)^3) q)‖^4 := by
  simp only [auxiliaryTraceIntegrand,auxiliaryTraceProduct,norm_mul,norm_pow,
    traceTorusCharacter,norm_latticeCharacter_eq_one,mul_one]

theorem auxiliary_field_character_eq_rational (γ : K) (p : 𝓞 K) (hp : p≠0)
    (target : 𝓞 K) :
    auxiliaryCubicCharacterContribution (fieldCenterCubicCharacter γ) p hp target =
      rationalCenterAuxiliaryContribution (fieldRationalCenter γ) p hp target := by
  rw [rationalCenterAuxiliaryContribution,← fieldPowerCharacter_center γ,
    Equiv.symm_apply_apply]
  rfl

def auxiliaryMajorScale (P : ℝ) (p : ℕ) : ℝ :=
  (P^finrank ℚ K)^5/((p:ℝ)^finrank ℚ K)^4

theorem auxiliaryMajorScale_pos (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) :
    0<auxiliaryMajorScale (K := K) P p := by
  dsimp [auxiliaryMajorScale]
  exact div_pos (pow_pos (pow_pos hP _) _) (pow_pos (pow_pos (Nat.cast_pos.mpr hp) _) _)

#print axioms auxiliaryTraceIntegrand_continuous
#print axioms auxiliary_field_character_eq_rational
end WaringSiegel.WSL4
