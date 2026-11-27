import WaringSiegel.WSL3MomentRepresentationSmooth

/-!
# A concrete major-arc lower bound now implies the exact representation

The minor contribution is a proved estimate at the optimized threshold.
The only remaining analytic premise in this bridge is a lower bound for
the actual major-arc integral, for the same positive smooth weight, scale,
and target character. Positivity and the target norm bound are conclusions.
-/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem one_le_rootScale {target : 𝓞 K} (htarget : target≠0) (k : ℕ) :
    1≤rootScale k target := by
  unfold rootScale
  exact Real.one_le_rpow (one_le_absNorm_integer htarget) (by positivity)

theorem representable_of_smoothRootMajor_dominance
    (k s : ℕ) (hk : 3≤k) (hs : 0<s)
    (hvariables : Thresholds.sufficientVariables k ≤ (s:ℤ))
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) :
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (target : 𝓞 K) (htarget : target≠0),
      C*((rootScale k target)^finrank ℚ K : ℝ)^((s:ℝ)-k-η) <
        (∫ q in traceMajorArcUnion ((rootScale k target)^k)
          ((k:ℝ)^finrank ℚ K*(rootScale k target)^finrank ℚ K),
          (compactTraceWeylSum k (smoothWeightSchwartz ρ R hρ hR)
            (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR)
            (rootScale k target) (rootScale_pos htarget k).ne' q)^s *
            traceTorusCharacter (-target) q ∂traceHaar).re →
      RepresentableByAtMost k s ((2*R)^finrank ℚ K) target := by
  obtain ⟨C,η,hC,hη,hminor⟩ := compactTraceWeylSum_fourier_minor_saving (K := K) k s hk hs hvariables
    (fun _ => smoothWeightSchwartz ρ R hρ hR)
    (fun _ => smoothWeightSchwartz_hasCompactSupport ρ R hρ hR)
  refine ⟨C,η,hC,hη,?_⟩
  intro target htarget hmajor
  let P := rootScale k target
  have hP0 : 0<P := rootScale_pos htarget k
  have hP : 1≤P := one_le_rootScale htarget k
  let g (q : ArchimedeanTraceTorus K) : ℂ :=
    (compactTraceWeylSum k (smoothWeightSchwartz ρ R hρ hR)
      (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) P hP0.ne' q)^s *
      traceTorusCharacter (-target) q
  have hg : Continuous g := ((compactTraceWeylSum_continuous _ _ _ _ _).pow s).mul
    (traceTorusCharacter_continuous _)
  have hig : Integrable g traceHaar :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsplit := integral_add_compl (vinogradovMinorArcs_measurable (K := K) k P hP0) hig
  have hnorm : ‖∫ q in vinogradovMinorArcs (K := K) k P, g q ∂traceHaar‖ ≤
      C*(P^finrank ℚ K : ℝ)^((s:ℝ)-k-η) := by
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hminor P hP target
  have hmain : C*(P^finrank ℚ K : ℝ)^((s:ℝ)-k-η) <
      (∫ q in (vinogradovMinorArcs (K := K) k P)ᶜ, g q ∂traceHaar).re := by
    simpa only [vinogradovMinorArcs,compl_compl] using hmajor
  have hlo := (abs_le.mp (Complex.abs_re_le_norm
    (∫ q in vinogradovMinorArcs (K := K) k P, g q ∂traceHaar))).1
  apply representable_of_smoothRootFourier_pos k s (by omega) target htarget ρ R hρ hR
  change 0 < (∫ q, g q ∂traceHaar).re
  rw [← hsplit,Complex.add_re]
  linarith

#print axioms representable_of_smoothRootMajor_dominance
end WaringSiegel.WSL3
