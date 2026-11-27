import WaringSiegel.WSL4AuxiliaryMinorPointwise
import WaringSiegel.WSL4SmoothMixedBound
import WaringSiegel.WSL4MajorAuxiliaryCoefficient

/-! # The actual outer minor coefficient has the required auxiliary-prime saving -/
noncomputable section
set_option maxHeartbeats 1400000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

def auxiliaryMinorCoefficient (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) (L : ℝ) (target : 𝓞 K) : ℂ :=
  ∫q in (traceMajorArcUnion (P^3) L)ᶜ,
    auxiliaryTraceIntegrand ρ R hρ hR P hP p hp target q ∂traceHaar

theorem auxiliaryFourier_eq_major_add_minor
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) (L : ℝ) (target : 𝓞 K) :
    (∫q,auxiliaryTraceIntegrand ρ R hρ hR P hP p hp target q ∂traceHaar) =
      auxiliaryMajorCoefficient ρ R hρ hR P hP p hp L target +
        auxiliaryMinorCoefficient ρ R hρ hR P hP p hp L target := by
  have hi : Integrable (auxiliaryTraceIntegrand ρ R hρ hR P hP p hp target) traceHaar :=
    (auxiliaryTraceIntegrand_continuous ρ R hρ hR P hP p hp target).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  exact (integral_add_compl (traceMajorArcUnion_measurableSet _ _ (pow_pos hP 3)) hi).symm

theorem auxiliaryMinorCoefficient_bound
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ) (hP : 1≤P) (p : ℕ) (hp : p.Prime),
      (p:ℝ)^7≤P → ∀target:𝓞 K,
      ‖auxiliaryMinorCoefficient ρ R hρ hR P (lt_of_lt_of_le zero_lt_one hP)
        p hp.pos (auxiliaryBroadConstant K R*P^finrank ℚ K) target‖ ≤
        C*(P^finrank ℚ K:ℝ)^(5+ε)*((p:ℝ)^finrank ℚ K:ℝ)^(-(9/2):ℝ) := by
  obtain ⟨A,hA,hpoint⟩ := smoothCoprimeCubicSum_minor_square_bound (K:=K)
    ρ R hρ hR (ε/2) (by positivity)
  obtain ⟨B,hB,hmoment⟩ := smoothAuxiliaryMixedMoment_bound (K:=K)
    ρ R hρ hR (ε/2) (by positivity)
  refine ⟨A*B,by positivity,?_⟩
  intro P hP p hp hpow target
  have hP0 : 0<P := lt_of_lt_of_le zero_lt_one hP
  let X := P^finrank ℚ K
  let Y := (p:ℝ)^finrank ℚ K
  let F : ArchimedeanTraceTorus K→ℂ :=
    fun q => compactCoprimeTraceCubicSum (smoothWeightSchwartz ρ R hρ hR) P p q 0
  let G : ArchimedeanTraceTorus K→ℂ :=
    fun q => smoothTraceSource 3 ρ R hρ hR (P/(p:ℝ))
      (div_pos hP0 (Nat.cast_pos.mpr hp.pos)).ne' (traceTorusMul ((p:𝓞 K)^3) q)
  let H : ArchimedeanTraceTorus K→ℝ := fun q => ‖F q‖^2*‖G q‖^4
  let S := (traceMajorArcUnion (K:=K) (P^3) (auxiliaryBroadConstant K R*X))ᶜ
  let D := A*X^((3:ℝ)/2+ε/2)
  have hF : Continuous F := by
    dsimp only [F]
    simp_rw [compactCoprimeTraceCubicSum_zero_eq (smoothWeightSchwartz ρ R hρ hR)
      (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) P hP0.ne']
    exact traceCoprimeWeylSum_continuous _ _ _ _
  have hG : Continuous G :=
    (smoothTraceSource_continuous _ _ _ _ _ _ _).comp (traceTorusMul_continuous _)
  have hH : Integrable H traceHaar := ((hF.norm.pow 2).mul (hG.norm.pow 4)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hH0 : ∀q,0≤H q := fun q => mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg _) 4)
  have hS : MeasurableSet S := (traceMajorArcUnion_measurableSet _ _ (pow_pos hP0 3)).compl
  have hi : Integrable (auxiliaryTraceIntegrand ρ R hρ hR P hP0 p hp.pos target) traceHaar :=
    (auxiliaryTraceIntegrand_continuous ρ R hρ hR P hP0 p hp.pos target).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hD : 0≤D := by dsimp [D,X]; positivity
  have hbound : (∫q,H q ∂traceHaar)≤B*X^((7:ℝ)/2+ε/2)*Y^(-(9/2):ℝ) :=
    hmoment P hP0 p hp.pos hpow
  change ‖∫q in S,auxiliaryTraceIntegrand ρ R hρ hR P hP0 p hp.pos target q ∂traceHaar‖≤_
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫q in S,D*H q ∂traceHaar := by
      apply setIntegral_mono_on hi.norm.integrableOn (hH.const_mul D).integrableOn hS
      intro q hq
      rw [auxiliaryTraceIntegrand_norm]
      change ‖F q‖^4*‖G q‖^4≤D*H q
      calc
        _ = ‖F q‖^2*H q := by dsimp [H]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (hpoint P hP p hp q hq) (hH0 q)
    _ = D*∫q in S,H q ∂traceHaar := integral_const_mul _ _
    _ ≤ D*∫q,H q ∂traceHaar := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hH (Filter.Eventually.of_forall hH0)) hD
    _ ≤ D*(B*X^((7:ℝ)/2+ε/2)*Y^(-(9/2):ℝ)) :=
      mul_le_mul_of_nonneg_left hbound hD
    _ = _ := by
      dsimp only [D]
      have he : X^((3:ℝ)/2+ε/2)*X^((7:ℝ)/2+ε/2)=X^(5+ε) := by
        rw [← Real.rpow_add (pow_pos hP0 _)]
        congr 1
        ring
      calc
        _ = (A*B)*(X^((3:ℝ)/2+ε/2)*X^((7:ℝ)/2+ε/2))*Y^(-(9/2):ℝ) := by ring
        _ = _ := by rw [he]

#print axioms auxiliaryFourier_eq_major_add_minor
#print axioms auxiliaryMinorCoefficient_bound
end WaringSiegel.WSL4Local
