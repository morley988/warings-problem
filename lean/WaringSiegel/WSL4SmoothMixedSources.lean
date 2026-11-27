import WaringSiegel.WSL4MixedPowerMask
import WaringSiegel.WSL4MixedSixthMonotone
import WaringSiegel.WSL4MajorSources
import WaringSiegel.WSL4CoprimeCubicWeyl

/-! # The literal smooth auxiliary mixed moment and its finite box majorant -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem compactCoprimeTraceCubicSum_zero_eq
    (w : mixedSpace K→ℂ) (hc : HasCompactSupport w)
    (P : ℝ) (hP : P≠0) (p : ℕ) (q : ArchimedeanTraceTorus K) :
    compactCoprimeTraceCubicSum w P p q 0 =
      traceCoprimeWeylSum (p:𝓞 K) 3
        (fun x : compactIntegerSupport w hc P hP => x.val)
        (fun x => w (P⁻¹ • mixedEmbedding K (x.val:K))) q := by
  rw [compactCoprimeTraceCubicSum_eq_finite w hc P hP]
  simp only [finiteLinearTraceSum,traceCoprimeWeylSum,traceTorusCharacter_zero,mul_one,
    Finset.sum_filter]
  exact (Finset.sum_coe_sort (compactIntegerSupport w hc P hP)
    (fun x : 𝓞 K => if IsUnit (Ideal.Quotient.mk (Ideal.span ({(p:𝓞 K)}:Set (𝓞 K))) x)
      then w (P⁻¹ • mixedEmbedding K (x:K))*traceTorusCharacter (x^3) q else 0)).symm

theorem smoothWeightSchwartz_support_norm
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (x : mixedSpace K)
    (hx : smoothWeightSchwartz ρ R hρ hR x≠0) : ‖x‖≤2*R := by
  have hs := smoothWeightSchwartz_support_subset ρ R hρ hR hx
  exact (mixed_norm_le_iff x (2*R)).mpr (fun v => (hs.1 v).2)

theorem smoothIntegerSupport_norm
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (P : ℝ) (hP : 0<P)
    (x : 𝓞 K) (hx : x∈compactIntegerSupport
      (smoothWeightSchwartz ρ R hρ hR)
      (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) P hP.ne') :
    ‖mixedEmbedding K (x:K)‖≤P*(2*R) := by
  have hs := smoothWeightSchwartz_support_subset ρ R hρ hR
    ((mem_compactIntegerSupport _ _ _ _ _).mp hx)
  apply (mixed_norm_le_iff _ _).mpr
  intro v
  rw [normAtPlace_apply]
  exact scaledIntegerNodeSet_place_bound hP hs v

theorem infinitePlace_natCast (p : ℕ) (v : InfinitePlace K) :
    v (p:K)=(p:ℝ) := by
  rw [← InfinitePlace.norm_embedding_eq,map_natCast,Complex.norm_natCast]

theorem mixedEmbedding_natCast_norm_le (p : ℕ) :
    ‖mixedEmbedding K (p:K)‖≤(p:ℝ) := by
  apply (mixed_norm_le_iff _ _).mpr
  intro v
  rw [normAtPlace_apply,infinitePlace_natCast]

def smoothAuxiliaryMixedMoment (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) : ℝ :=
  ∫q, ‖compactCoprimeTraceCubicSum (smoothWeightSchwartz ρ R hρ hR) P p q 0‖^2 *
    ‖smoothTraceSource 3 ρ R hρ hR (P/(p:ℝ))
      (div_pos hP (Nat.cast_pos.mpr hp)).ne' (traceTorusMul ((p:𝓞 K)^3) q)‖^4 ∂traceHaar

theorem smoothAuxiliaryMixedMoment_le_unweighted
    (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R)
    (P : ℝ) (hP : 0<P) (p : ℕ) (hp : 0<p) :
    smoothAuxiliaryMixedMoment (K:=K) ρ R hρ hR P hP p hp ≤
      ∫q, ‖traceCoprimeWeylSum (p:𝓞 K) 3
          (fun x : compactIntegerSupport (smoothWeightSchwartz ρ R hρ hR)
            (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) P hP.ne' => x.val)
          (fun _ => 1) q‖^2 *
        ‖traceWeylSum 3
          (fun y : compactIntegerSupport (smoothWeightSchwartz ρ R hρ hR)
            (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) (P/(p:ℝ))
              (div_pos hP (Nat.cast_pos.mpr hp)).ne' => y.val)
          (fun _ => 1) (traceTorusMul ((p:𝓞 K)^3) q)‖^4 ∂traceHaar := by
  let X := compactIntegerSupport (smoothWeightSchwartz (K:=K) ρ R hρ hR)
    (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) P hP.ne'
  let Y := compactIntegerSupport (smoothWeightSchwartz (K:=K) ρ R hρ hR)
    (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) (P/(p:ℝ))
      (div_pos hP (Nat.cast_pos.mpr hp)).ne'
  have hb := trace_coprime_mixed_sixth_le_unweighted ((p:𝓞 K)^3)
    (fun x:X => x.val) (fun y:Y => y.val)
    (fun x => smoothRootWeight ρ R (P⁻¹ • mixedEmbedding K (x.val:K)))
    (fun y => smoothRootWeight ρ R ((P/(p:ℝ))⁻¹ • mixedEmbedding K (y.val:K)))
    1 1 zero_le_one zero_le_one
    (fun _ => smoothRootWeight_nonneg _ _ _) (fun _ => smoothRootWeight_le_one _ _ _)
    (fun _ => smoothRootWeight_nonneg _ _ _) (fun _ => smoothRootWeight_le_one _ _ _)
  simp only [traceCoprimeWeylSum_power_modulus _ 3 (by norm_num),one_pow,one_mul] at hb
  simpa only [smoothAuxiliaryMixedMoment,compactCoprimeTraceCubicSum_zero_eq
    (smoothWeightSchwartz ρ R hρ hR)
    (smoothWeightSchwartz_hasCompactSupport ρ R hρ hR) P hP.ne',
    smoothTraceSource,compactTraceWeylSum,smoothWeightSchwartz_apply] using hb

#print axioms compactCoprimeTraceCubicSum_zero_eq
#print axioms smoothIntegerSupport_norm
#print axioms smoothAuxiliaryMixedMoment_le_unweighted
end WaringSiegel.WSL4Local
