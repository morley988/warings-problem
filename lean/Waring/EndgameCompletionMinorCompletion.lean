import Waring.EndgameCompletionMinorMoments

/-!
# Common-kernel completion before the lower-degree projection

Weighted Jensen is applied to each actual completed finite sum and then
integrated over the lower coefficient torus. Fubini uses continuity on the
compact torus times the compact integration interval.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace Waring.EndgameCompletion
open FourierCompletion

theorem integrable_torus_unit_interval {r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : UnitAddTorus (Fin r)×ℝ→E) (hF : Continuous F) :
    Integrable F ((unitTorusMeasure r).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  have hi : IntegrableOn F (Set.univ×ˢSet.Icc (0 : ℝ) 1)
      ((unitTorusMeasure r).prod volume) :=
    hF.continuousOn.integrableOn_compact (isCompact_univ.prod isCompact_Icc)
  have hj := hi.mono_set (Set.prod_mono (Set.Subset.refl Set.univ) Set.Ioc_subset_Icc_self)
  simpa only [IntegrableOn,← Measure.prod_restrict,Measure.restrict_univ] using hj

theorem integral_torus_unit_interval_swap {r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : UnitAddTorus (Fin r)×ℝ→E) (hF : Continuous F) :
    (∫ α,(∫ t in (0 : ℝ)..1,F (α,t)) ∂unitTorusMeasure r)=
      ∫ t in (0 : ℝ)..1,∫ α,F (α,t) ∂unitTorusMeasure r := by
  simpa only [intervalIntegral.integral_of_le zero_le_one] using
    integral_integral_swap (f := fun α t=>F (α,t)) (integrable_torus_unit_interval F hF)

theorem continuous_torus_modulatedSum {r : ℕ} (S : Finset ℤ)
    (w : UnitAddTorus (Fin r)→ℤ→ℂ)
    (hw : ∀ n,Continuous (fun α=>w α n)) :
    Continuous (fun z : UnitAddTorus (Fin r)×ℝ=>modulatedSum S (w z.1) z.2) := by
  unfold modulatedSum
  exact continuous_finset_sum _ (fun n _=>(hw n).comp continuous_fst |>.mul
    (((fourier n).continuous.comp (AddCircle.continuous_mk' 1)).comp continuous_snd))

/-- Integrated completion with one fixed kernel and one common modulation.
Only continuity and the literal kernel domination are required. -/
theorem torus_family_completion (r p : ℕ) (hp : 1≤p)
    (S T : Finset ℤ) (hTS : T⊆S)
    (w : UnitAddTorus (Fin r)→ℤ→ℂ)
    (hw : ∀ n,Continuous (fun α=>w α n))
    (K : ℝ→ℝ) (hKc : Continuous K) (hK0 : ∀ t,0≤K t)
    (hkernel : ∀ t,‖kernel T t‖≤K t) :
    (∫ α,‖∑ n∈T,w α n‖^p ∂unitTorusMeasure r)≤
      (∫ t in (0 : ℝ)..1,K t)^(p-1)*
        (∫ t in (0 : ℝ)..1,K t*
          (∫ α,‖modulatedSum S (w α) t‖^p ∂unitTorusMeasure r)) := by
  let A := ∫ t in (0 : ℝ)..1,K t
  have hA : 0≤A := intervalIntegral.integral_nonneg zero_le_one (fun t _=>hK0 t)
  have hKi : IntervalIntegrable K volume 0 1 := hKc.intervalIntegrable 0 1
  let F := fun z : UnitAddTorus (Fin r)×ℝ=>K z.2*‖modulatedSum S (w z.1) z.2‖^p
  have hF : Continuous F := (hKc.comp continuous_snd).mul
    ((continuous_torus_modulatedSum S w hw).norm.pow p)
  have hFi := integrable_torus_unit_interval F hF
  have hleft : Integrable (fun α=>‖∑ n∈T,w α n‖^p) (unitTorusMeasure r) :=
    integrable_continuous_torus _ ((continuous_finset_sum _ (fun n _=>hw n)).norm.pow p)
  have hright : Integrable
      (fun α=>A^(p-1)*(∫ t in (0 : ℝ)..1,F (α,t))) (unitTorusMeasure r) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using
      hFi.integral_prod_left.const_mul (A^(p-1))
  calc
    _ ≤ ∫ α,A^(p-1)*(∫ t in (0 : ℝ)..1,F (α,t)) ∂unitTorusMeasure r := by
      apply integral_mono hleft hright
      intro α
      apply (pow_le_pow_left₀ (norm_nonneg _)
        (completion_common_majorant S T hTS (w α) K hKi (fun t _=>hkernel t)) p).trans
      exact integral_weighted_pow_le hp hKc.measurable hK0 hKi
        (continuous_modulatedSum S (w α)).norm (fun _=>norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul,integral_torus_unit_interval_swap F hF]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [F]
      rw [integral_const_mul]

def completionMass (N : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1,‖linearWeylSum N t‖

theorem continuous_linearWeylSum (N : ℕ) : Continuous (linearWeylSum N) :=
  continuous_finset_sum _ (fun n _=>
    (fourier (n : ℤ)).continuous.comp (AddCircle.continuous_mk' 1))

theorem completionMass_nonneg (N : ℕ) : 0≤completionMass N :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _=>norm_nonneg _)

theorem norm_kernel_integer_interval (N : ℕ) (a : ℤ) (t : ℝ) :
    ‖kernel (Finset.Icc (a+1) (a+N)) t‖=‖linearWeylSum N t‖ := by
  rw [interval_eq_progression]
  have hh : (a+(N : ℤ)+1-(a+1)).toNat=N := by omega
  rw [hh,norm_kernel_progression _ _ _ (by norm_num)]
  simp

theorem completionMass_le_dyadic (N : ℕ) (hN : 1≤N) :
    completionMass N≤4*((Nat.clog 2 N+1 : ℕ) : ℝ) := by
  have hNpos : 0<N := by omega
  apply (intervalIntegral.integral_mono_on zero_le_one
    ((continuous_linearWeylSum N).norm.intervalIntegrable 0 1)
    (CompletionKernel.kernel_intervalIntegrable hNpos 0 1) ?_).trans
    (CompletionKernel.kernel_integral_le_dyadic N (Nat.clog 2 N) hNpos
      (by exact_mod_cast Nat.le_pow_clog (by norm_num : 1<2) N))
  intro t _
  calc
    _ ≤ linearSumBound N t := by
      rw [← norm_shiftedLinearWeylSum 0]
      exact norm_shiftedLinearWeylSum_le 0 N t
    _ ≤ _ := CompletionKernel.linearSumBound_le_kernel_of_le N N le_rfl t

#print axioms torus_family_completion
#print axioms completionMass_le_dyadic
end Waring.EndgameCompletion
