import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Repeated nonstationary integration by parts with compact parameters

A globally smooth reciprocal directional phase derivative gives an actual
uniform oscillatory tail. The iterated amplitudes have a common compact
support and depend smoothly on the parameter, so their L¹ norms are bounded
uniformly over each compact parameter family.
-/
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ContDiff
namespace WaringSiegel.WSL3
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 800000

/-- Each step differentiates the amplitude multiplied by a reciprocal
phase derivative, in the chosen parameter-dependent source direction. -/
def nonstationaryAmplitude (A : P × E → ℂ) (v : P → E) (f : E → ℂ) : ℕ → P × E → ℂ
  | 0 => fun p => f p.2
  | n+1 => fun p => fderiv ℝ
      (fun x => A (p.1,x) * nonstationaryAmplitude A v f n (p.1,x)) p.2 (v p.1)

theorem nonstationaryAmplitude_contDiff {A : P × E → ℂ} {v : P → E} {f : E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (nonstationaryAmplitude A v f n) := by
  induction n with
  | zero => exact hf.comp contDiff_snd
  | succ n ih =>
      have hg : ContDiff ℝ ∞ (fun p : P × E => A p * nonstationaryAmplitude A v f n p) := hA.mul ih
      have hg' : ContDiff ℝ ∞ (fun q : (P × E) × E =>
          A (q.1.1,q.2) * nonstationaryAmplitude A v f n (q.1.1,q.2)) :=
        hg.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
      exact hg'.fderiv_apply contDiff_snd (hv.comp contDiff_fst) (by simp)

/-- The entire family retains the original fixed closed support. -/
theorem nonstationaryAmplitude_support {A : P × E → ℂ} {v : P → E} {f : E → ℂ}
    {S : Set E} (hS : IsClosed S) (hf : support f ⊆ S) (n : ℕ) (p : P) :
    support (fun x => nonstationaryAmplitude A v f n (p,x)) ⊆ S := by
  induction n with
  | zero => exact hf
  | succ n ih =>
      intro x hx
      let g : E → ℂ := fun y => A (p,y) * nonstationaryAmplitude A v f n (p,y)
      have hgs : support g ⊆ S := fun y hy => ih (mul_ne_zero_iff.mp hy).2
      have hxd : x ∈ support (fderiv ℝ g) := by
        intro hz
        apply hx
        change fderiv ℝ g x (v p) = 0
        rw [hz, ContinuousLinearMap.zero_apply]
      exact (closure_minimal hgs hS) (support_fderiv_subset ℝ hxd)

theorem nonstationaryAmplitude_hasCompactSupport {A : P × E → ℂ} {v : P → E} {f : E → ℂ}
    {S : Set E} (hS : IsCompact S) (hf : support f ⊆ S) (n : ℕ) (p : P) :
    HasCompactSupport (fun x => nonstationaryAmplitude A v f n (p,x)) :=
  HasCompactSupport.of_support_subset_isCompact hS
    (nonstationaryAmplitude_support hS.isClosed hf n p)

theorem nonstationaryAmplitude_uniform_bound {A : P × E → ℂ} {v : P → E} {f : E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f)
    {T : Set P} {S : Set E} (hT : IsCompact T) (hS : IsCompact S) (hfs : support f ⊆ S)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ x,
      ‖nonstationaryAmplitude A v f n (p,x)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := ((hT.prod hS).image
    (nonstationaryAmplitude_contDiff hA hv hf n).continuous).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun p hp x => ?_⟩
  by_cases hx : x ∈ S
  · exact hb _ (Set.mem_image_of_mem _ ⟨hp,hx⟩)
  · have hz : nonstationaryAmplitude A v f n (p,x) = 0 := by
      by_contra hn
      exact hx (nonstationaryAmplitude_support hS.isClosed hfs n p hn)
    simpa only [hz, norm_zero] using hC.le

/-- The real phase is multiplied by i*lambda, so its exponential has modulus one. -/
def scalarOscillatoryPhase (lambda : ℝ) (phi : E → ℝ) (x : E) : ℂ :=
  Complex.exp ((lambda : ℂ) * Complex.I * (phi x : ℂ))

theorem scalarOscillatoryPhase_norm (lambda : ℝ) (phi : E → ℝ) (x : E) :
    ‖scalarOscillatoryPhase lambda phi x‖ = 1 := by
  simp [scalarOscillatoryPhase, Complex.norm_exp]

theorem scalarOscillatoryPhase_contDiff (lambda : ℝ) {phi : E → ℝ}
    (hphi : ContDiff ℝ ∞ phi) : ContDiff ℝ ∞ (scalarOscillatoryPhase lambda phi) :=
  Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hphi))

theorem scalarOscillatoryPhase_fderiv (lambda : ℝ) {phi : E → ℝ}
    (hphi : Differentiable ℝ phi) (x z : E) :
    fderiv ℝ (scalarOscillatoryPhase lambda phi) x z =
      ((lambda : ℂ)*Complex.I) * (fderiv ℝ phi x z : ℂ) * scalarOscillatoryPhase lambda phi x := by
  have h := (((Complex.ofRealCLM.hasFDerivAt).comp x (hphi x).hasFDerivAt).const_mul
    ((lambda : ℂ)*Complex.I)).cexp
  change (fderiv ℝ (fun y => Complex.exp ((lambda : ℂ)*Complex.I*
    ((Complex.ofRealCLM ∘ phi) y))) x) z = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  change Complex.exp ((lambda : ℂ)*Complex.I*(phi x : ℂ)) *
    ((lambda : ℂ)*Complex.I*(fderiv ℝ phi x z : ℂ)) = _
  unfold scalarOscillatoryPhase
  ring

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem nonstationaryAmplitude_integrable {A : P × E → ℂ} {v : P → E} {f : E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f)
    {S : Set E} (hS : IsCompact S) (hfs : support f ⊆ S) (n : ℕ) (p : P) :
    Integrable (fun x => nonstationaryAmplitude A v f n (p,x)) :=
  ((nonstationaryAmplitude_contDiff hA hv hf n).continuous.comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (nonstationaryAmplitude_hasCompactSupport hS hfs n p)

theorem nonstationaryAmplitude_phase_integrable {A : P × E → ℂ} {v : P → E} {f : E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f)
    {S : Set E} (hS : IsCompact S) (hfs : support f ⊆ S)
    (n : ℕ) (p : P) (lambda : ℝ) {phi : E → ℝ} (hphi : ContDiff ℝ ∞ phi) :
    Integrable (fun x => nonstationaryAmplitude A v f n (p,x) * scalarOscillatoryPhase lambda phi x) := by
  have hc : Continuous (fun x => nonstationaryAmplitude A v f n (p,x) *
      scalarOscillatoryPhase lambda phi x) :=
    ((nonstationaryAmplitude_contDiff hA hv hf n).continuous.comp
      (continuous_const.prodMk continuous_id)).mul (scalarOscillatoryPhase_contDiff lambda hphi).continuous
  exact hc.integrable_of_hasCompactSupport
    (nonstationaryAmplitude_hasCompactSupport hS hfs n p).mul_right

/-- One exact integration-by-parts step. The reciprocal identity is needed
only on the common source support. -/
theorem nonstationary_step {A : P × E → ℂ} {v : P → E} {f : E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f)
    {S : Set E} (hS : IsCompact S) (hfs : support f ⊆ S)
    (n : ℕ) (p : P) (lambda : ℝ) {phi : E → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hrecip : ∀ x ∈ S, A (p,x) * (fderiv ℝ phi x (v p) : ℂ) = 1) :
    ((lambda : ℂ)*Complex.I) *
      (∫ x, nonstationaryAmplitude A v f n (p,x) * scalarOscillatoryPhase lambda phi x) =
      -(∫ x, nonstationaryAmplitude A v f (n+1) (p,x) * scalarOscillatoryPhase lambda phi x) := by
  let g : E → ℂ := fun x => A (p,x) * nonstationaryAmplitude A v f n (p,x)
  have hg : ContDiff ℝ ∞ g := (hA.mul (nonstationaryAmplitude_contDiff hA hv hf n)).comp
    (contDiff_const.prodMk contDiff_id)
  have hgc : HasCompactSupport g := (nonstationaryAmplitude_hasCompactSupport hS hfs n p).mul_left
  have he (x : E) : g x * fderiv ℝ (scalarOscillatoryPhase lambda phi) x (v p) =
      ((lambda : ℂ)*Complex.I) *
        (nonstationaryAmplitude A v f n (p,x) * scalarOscillatoryPhase lambda phi x) := by
    rw [scalarOscillatoryPhase_fderiv lambda (hphi.differentiable (by simp))]
    by_cases hx : x ∈ S
    · have hr := hrecip x hx
      dsimp only [g]
      calc
        _ = ((lambda : ℂ)*Complex.I) *
            (A (p,x)*(fderiv ℝ phi x (v p) : ℂ)) *
            (nonstationaryAmplitude A v f n (p,x) * scalarOscillatoryPhase lambda phi x) := by ring
        _ = _ := by rw [hr, mul_one]
    · have hz : nonstationaryAmplitude A v f n (p,x) = 0 := by
        by_contra hn
        exact hx (nonstationaryAmplitude_support hS.isClosed hfs n p hn)
      simp only [g, hz, mul_zero, zero_mul]
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure E))
    (v := v p)
    (nonstationaryAmplitude_phase_integrable hA hv hf hS hfs (n+1) p lambda hphi)
    (by
      have h := (nonstationaryAmplitude_phase_integrable hA hv hf hS hfs n p lambda hphi).const_mul
        ((lambda : ℂ)*Complex.I)
      exact h.congr (Eventually.of_forall fun x => (he x).symm))
    ((hg.continuous.mul (scalarOscillatoryPhase_contDiff lambda hphi).continuous).integrable_of_hasCompactSupport hgc.mul_right)
    (hg.differentiable (by simp)) ((scalarOscillatoryPhase_contDiff lambda hphi).differentiable (by simp))
  simpa only [he, integral_const_mul] using hi

/-- Iteration is an exact identity of norms, including at zero frequency. -/
theorem nonstationary_iterate_norm {A : P × E → ℂ} {v : P → E} {f : E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f)
    {S : Set E} (hS : IsCompact S) (hfs : support f ⊆ S)
    (n : ℕ) (p : P) (lambda : ℝ) {phi : E → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hrecip : ∀ x ∈ S, A (p,x) * (fderiv ℝ phi x (v p) : ℂ) = 1) :
    |lambda|^n * ‖∫ x, f x * scalarOscillatoryPhase lambda phi x‖ =
      ‖∫ x, nonstationaryAmplitude A v f n (p,x) * scalarOscillatoryPhase lambda phi x‖ := by
  induction n with
  | zero => simp [nonstationaryAmplitude]
  | succ n ih =>
      have hs := congrArg norm (nonstationary_step hA hv hf hS hfs n p lambda hphi hrecip)
      simp only [norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs] at hs
      rw [pow_succ]
      calc
        _ = |lambda| * (|lambda|^n * ‖∫ x, f x * scalarOscillatoryPhase lambda phi x‖) := by ring
        _ = _ := by rw [ih, hs]

/-- Uniform arbitrary-power decay for an actual compactly supported
oscillatory integral, with its reciprocal phase derivative supplied smoothly
on a compact parameter family. All integrability hypotheses are derived. -/
theorem uniform_nonstationary_integral_bound
    {A : P × E → ℂ} {v : P → E} {f : E → ℂ} {phi : P → E → ℝ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hf : ContDiff ℝ ∞ f)
    {T : Set P} {S : Set E} (hT : IsCompact T) (hS : IsCompact S) (hfs : support f ⊆ S)
    (hphi : ∀ p ∈ T, ContDiff ℝ ∞ (phi p))
    (hrecip : ∀ p ∈ T, ∀ x ∈ S, A (p,x) * (fderiv ℝ (phi p) x (v p) : ℂ) = 1)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ lambda : ℝ,
      |lambda|^n * ‖∫ x, f x * scalarOscillatoryPhase lambda (phi p) x‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := nonstationaryAmplitude_uniform_bound hA hv hf hT hS hfs n
  refine ⟨B * volume.real S + 1, by positivity, fun p hp lambda => ?_⟩
  rw [nonstationary_iterate_norm hA hv hf hS hfs n p lambda (hphi p hp) (hrecip p hp)]
  have he : (∫ x in S, nonstationaryAmplitude A v f n (p,x) *
      scalarOscillatoryPhase lambda (phi p) x) =
      ∫ x, nonstationaryAmplitude A v f n (p,x) * scalarOscillatoryPhase lambda (phi p) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have hz : nonstationaryAmplitude A v f n (p,x) = 0 := by
        by_contra hn
        exact hx (nonstationaryAmplitude_support hS.isClosed hfs n p hn)
      rw [hz, zero_mul]
  rw [← he]
  have hbound := norm_setIntegral_le_of_norm_le_const_ae (μ := (volume : Measure E))
    hS.measure_lt_top (Eventually.of_forall fun x => show
      ‖nonstationaryAmplitude A v f n (p,x) * scalarOscillatoryPhase lambda (phi p) x‖ ≤ B from by
        simpa only [norm_mul, scalarOscillatoryPhase_norm, mul_one] using hb p hp x)
  exact hbound.trans (le_add_of_nonneg_right zero_le_one)

#print axioms uniform_nonstationary_integral_bound

end WaringSiegel.WSL3
