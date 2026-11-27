import WaringSiegel.WSL4WeilRepresentationSources
import WaringSiegel.WSL4MajorAuxiliarySources

/-! # The actual auxiliary Fourier coefficient implies eight cubes

The two finite node families are the unit-masked roots at scale P and p times
the roots at scale P/p. Both normalize into the same positive root box.
-/
noncomputable section
set_option maxHeartbeats 1400000
namespace WaringSiegel.WSL4Weil
open MeasureTheory NumberField NumberField.mixedEmbedding Module
  WSL2 WSL3 WSL3Poisson WSL4Local WSL4
open scoped NumberField BigOperators Classical SchwartzMap
variable {K : Type*} [Field K] [NumberField K]

theorem representable_eight_cubes_of_auxiliaryFourier_ne_zero
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (target : 𝓞 K) (htarget : target ≠ 0) (p : ℕ) (hp : 0 < p)
    (hne : (∫ q, auxiliaryTraceIntegrand ρ R hρ hR
      (rootScale 3 target) (rootScale_pos htarget 3) p hp target q ∂traceHaar) ≠ 0) :
    RepresentableByAtMost 3 8 ((2*R)^finrank ℚ K) target := by
  let w : mixedSpace K → ℂ := smoothWeightSchwartz ρ R hρ hR
  have hc : HasCompactSupport w := smoothWeightSchwartz_hasCompactSupport ρ R hρ hR
  let P := rootScale 3 target
  have hP : 0 < P := rootScale_pos htarget 3
  have hPp : P/(p : ℝ) ≠ 0 := (div_pos hP (Nat.cast_pos.mpr hp)).ne'
  let A := maskedIntegerSupport w hc P hP.ne' p
  let B := compactIntegerSupport w hc (P/(p : ℝ)) hPp
  let a : A → 𝓞 K := fun x => x.val
  let b : B → 𝓞 K := fun x => (p : 𝓞 K)*x.val
  let wa : A → ℂ := fun x => w (P⁻¹ • mixedEmbedding K (x.val : K))
  let wb : B → ℂ := fun x => w ((P/(p : ℝ))⁻¹ • mixedEmbedding K (x.val : K))
  have hf (q : ArchimedeanTraceTorus K) :
      compactCoprimeTraceCubicSum w P p q 0 = traceWeylSum 3 a wa q :=
    compactCoprimeTraceCubicSum_eq_traceWeylSum w hc P hP.ne' p q
  have hg (q : ArchimedeanTraceTorus K) :
      smoothTraceSource 3 ρ R hρ hR (P/(p : ℝ)) hPp
        (traceTorusMul ((p : 𝓞 K)^3) q) = traceWeylSum 3 b wb q :=
    compactTraceCubicSum_mul_eq_scaled_nodes w hc (P/(p : ℝ)) hPp p q
  have hne' : (∫ q, (traceWeylSum 3 a wa q)^4*(traceWeylSum 3 b wb q)^4*
      traceTorusCharacter (-target) q ∂traceHaar) ≠ 0 := by
    change (∫ q, (compactCoprimeTraceCubicSum w P p q 0)^4*
      (smoothTraceSource 3 ρ R hρ hR (P/(p : ℝ)) hPp
        (traceTorusMul ((p : 𝓞 K)^3) q))^4*
      traceTorusCharacter (-target) q ∂traceHaar) ≠ 0 at hne
    simpa only [hf,hg] using hne
  obtain ⟨x,hx,hsum⟩ := four_by_four_fourier_ne_zero_has_solution 3 a b wa wb target hne'
  have hbox (i : Fin 8) : x i ∈ scaledIntegerNodeSet P (ρ/2) (2*R) := by
    rcases hx i with ⟨u,hu⟩ | ⟨u,hu⟩
    · rw [hu]
      exact smoothWeightSchwartz_support_subset ρ R hρ hR
        ((mem_compactIntegerSupport w hc P hP.ne' u.val).mp
          (Finset.mem_filter.mp u.property).1)
    · rw [hu]
      change P⁻¹ • mixedEmbedding K (((p : 𝓞 K)*u.val : 𝓞 K) : K) ∈ rootBox K (ρ/2) (2*R)
      rw [inverse_scale_prime_mul_embedding]
      exact smoothWeightSchwartz_support_subset ρ R hρ hR
        ((mem_compactIntegerSupport w hc (P/(p : ℝ)) hPp u.val).mp u.property)
  refine ⟨8,le_rfl,x,?_,hsum,?_⟩
  · intro i σ
    exact (scaledIntegerNodeSet_positive hP (by positivity) (hbox i) σ).le
  · intro i
    exact scaledIntegerNodeSet_target_norm_bound 3 (by norm_num) htarget (hbox i)

theorem representable_eight_cubes_of_auxiliaryFourier_pos
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (target : 𝓞 K) (htarget : target ≠ 0) (p : ℕ) (hp : 0 < p)
    (hpos : 0 < (∫ q, auxiliaryTraceIntegrand ρ R hρ hR
      (rootScale 3 target) (rootScale_pos htarget 3) p hp target q ∂traceHaar).re) :
    RepresentableByAtMost 3 8 ((2*R)^finrank ℚ K) target := by
  apply representable_eight_cubes_of_auxiliaryFourier_ne_zero ρ R hρ hR target htarget p hp
  intro hz
  rw [hz,Complex.zero_re] at hpos
  exact lt_irrefl _ hpos
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.representable_eight_cubes_of_auxiliaryFourier_ne_zero
#print axioms WaringSiegel.WSL4Weil.representable_eight_cubes_of_auxiliaryFourier_pos
