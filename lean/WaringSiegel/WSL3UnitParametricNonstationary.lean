import WaringSiegel.WSL3UnitNonstationaryCore

/-!
# Uniform integration by parts for smooth compact parameter amplitudes

The amplitude varies smoothly with the parameter, while all source supports
lie in one compact set. This covers translated products of a fixed weight.
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
def parameterNonstationaryAmplitude (A : P × E → ℂ) (v : P → E) (F : P × E → ℂ) : ℕ → P × E → ℂ
  | 0 => F
  | n+1 => fun p => fderiv ℝ
      (fun x => A (p.1,x) * parameterNonstationaryAmplitude A v F n (p.1,x)) p.2 (v p.1)

theorem parameterNonstationaryAmplitude_contDiff {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (parameterNonstationaryAmplitude A v F n) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
      have hg : ContDiff ℝ ∞ (fun p : P × E => A p * parameterNonstationaryAmplitude A v F n p) := hA.mul ih
      have hg' : ContDiff ℝ ∞ (fun q : (P × E) × E =>
          A (q.1.1,q.2) * parameterNonstationaryAmplitude A v F n (q.1.1,q.2)) :=
        hg.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
      exact hg'.fderiv_apply contDiff_snd (hv.comp contDiff_fst) (by simp)

/-- The entire family retains the original fixed closed support. -/
theorem parameterNonstationaryAmplitude_support {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    {S : Set E} (hS : IsClosed S) (hF : ∀ p, support (fun x => F (p,x)) ⊆ S) (n : ℕ) (p : P) :
    support (fun x => parameterNonstationaryAmplitude A v F n (p,x)) ⊆ S := by
  induction n with
  | zero => exact hF p
  | succ n ih =>
      intro x hx
      let g : E → ℂ := fun y => A (p,y) * parameterNonstationaryAmplitude A v F n (p,y)
      have hgs : support g ⊆ S := fun y hy => ih (mul_ne_zero_iff.mp hy).2
      have hxd : x ∈ support (fderiv ℝ g) := by
        intro hz
        apply hx
        change fderiv ℝ g x (v p) = 0
        rw [hz, ContinuousLinearMap.zero_apply]
      exact (closure_minimal hgs hS) (support_fderiv_subset ℝ hxd)

theorem parameterNonstationaryAmplitude_hasCompactSupport {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    {S : Set E} (hS : IsCompact S) (hF : ∀ p, support (fun x => F (p,x)) ⊆ S) (n : ℕ) (p : P) :
    HasCompactSupport (fun x => parameterNonstationaryAmplitude A v F n (p,x)) :=
  HasCompactSupport.of_support_subset_isCompact hS
    (parameterNonstationaryAmplitude_support hS.isClosed hF n p)

theorem parameterNonstationaryAmplitude_uniform_bound {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    {T : Set P} {S : Set E} (hT : IsCompact T) (hS : IsCompact S) (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ x,
      ‖parameterNonstationaryAmplitude A v F n (p,x)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := ((hT.prod hS).image
    (parameterNonstationaryAmplitude_contDiff hA hv hF n).continuous).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun p hp x => ?_⟩
  by_cases hx : x ∈ S
  · exact hb _ (Set.mem_image_of_mem _ ⟨hp,hx⟩)
  · have hz : parameterNonstationaryAmplitude A v F n (p,x) = 0 := by
      by_contra hn
      exact hx (parameterNonstationaryAmplitude_support hS.isClosed hFs n p hn)
    simpa only [hz, norm_zero] using hC.le

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

theorem parameterNonstationaryAmplitude_integrable {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    {S : Set E} (hS : IsCompact S) (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S) (n : ℕ) (p : P) :
    Integrable (fun x => parameterNonstationaryAmplitude A v F n (p,x)) :=
  ((parameterNonstationaryAmplitude_contDiff hA hv hF n).continuous.comp
    (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (parameterNonstationaryAmplitude_hasCompactSupport hS hFs n p)

theorem parameterNonstationaryAmplitude_phase_integrable {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    {S : Set E} (hS : IsCompact S) (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S)
    (n : ℕ) (p : P) (lambda : ℝ) {phi : E → ℝ} (hphi : ContDiff ℝ ∞ phi) :
    Integrable (fun x => parameterNonstationaryAmplitude A v F n (p,x) * scalarOscillatoryPhase lambda phi x) := by
  have hc : Continuous (fun x => parameterNonstationaryAmplitude A v F n (p,x) *
      scalarOscillatoryPhase lambda phi x) :=
    ((parameterNonstationaryAmplitude_contDiff hA hv hF n).continuous.comp
      (continuous_const.prodMk continuous_id)).mul (scalarOscillatoryPhase_contDiff lambda hphi).continuous
  exact hc.integrable_of_hasCompactSupport
    (parameterNonstationaryAmplitude_hasCompactSupport hS hFs n p).mul_right

/-- One exact integration-by-parts step. The reciprocal identity is needed
only on the common source support. -/
theorem parameter_nonstationary_step {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    {S : Set E} (hS : IsCompact S) (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S)
    (n : ℕ) (p : P) (lambda : ℝ) {phi : E → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hrecip : ∀ x ∈ S, A (p,x) * (fderiv ℝ phi x (v p) : ℂ) = 1) :
    ((lambda : ℂ)*Complex.I) *
      (∫ x, parameterNonstationaryAmplitude A v F n (p,x) * scalarOscillatoryPhase lambda phi x) =
      -(∫ x, parameterNonstationaryAmplitude A v F (n+1) (p,x) * scalarOscillatoryPhase lambda phi x) := by
  let g : E → ℂ := fun x => A (p,x) * parameterNonstationaryAmplitude A v F n (p,x)
  have hg : ContDiff ℝ ∞ g := (hA.mul (parameterNonstationaryAmplitude_contDiff hA hv hF n)).comp
    (contDiff_const.prodMk contDiff_id)
  have hgc : HasCompactSupport g := (parameterNonstationaryAmplitude_hasCompactSupport hS hFs n p).mul_left
  have he (x : E) : g x * fderiv ℝ (scalarOscillatoryPhase lambda phi) x (v p) =
      ((lambda : ℂ)*Complex.I) *
        (parameterNonstationaryAmplitude A v F n (p,x) * scalarOscillatoryPhase lambda phi x) := by
    rw [scalarOscillatoryPhase_fderiv lambda (hphi.differentiable (by simp))]
    by_cases hx : x ∈ S
    · have hr := hrecip x hx
      dsimp only [g]
      calc
        _ = ((lambda : ℂ)*Complex.I) *
            (A (p,x)*(fderiv ℝ phi x (v p) : ℂ)) *
            (parameterNonstationaryAmplitude A v F n (p,x) * scalarOscillatoryPhase lambda phi x) := by ring
        _ = _ := by rw [hr, mul_one]
    · have hz : parameterNonstationaryAmplitude A v F n (p,x) = 0 := by
        by_contra hn
        exact hx (parameterNonstationaryAmplitude_support hS.isClosed hFs n p hn)
      simp only [g, hz, mul_zero, zero_mul]
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure E))
    (v := v p)
    (parameterNonstationaryAmplitude_phase_integrable hA hv hF hS hFs (n+1) p lambda hphi)
    (by
      have h := (parameterNonstationaryAmplitude_phase_integrable hA hv hF hS hFs n p lambda hphi).const_mul
        ((lambda : ℂ)*Complex.I)
      exact h.congr (Eventually.of_forall fun x => (he x).symm))
    ((hg.continuous.mul (scalarOscillatoryPhase_contDiff lambda hphi).continuous).integrable_of_hasCompactSupport hgc.mul_right)
    (hg.differentiable (by simp)) ((scalarOscillatoryPhase_contDiff lambda hphi).differentiable (by simp))
  simpa only [he, integral_const_mul] using hi

/-- Iteration is an exact identity of norms, including at zero frequency. -/
theorem parameter_nonstationary_iterate_norm {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    {S : Set E} (hS : IsCompact S) (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S)
    (n : ℕ) (p : P) (lambda : ℝ) {phi : E → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hrecip : ∀ x ∈ S, A (p,x) * (fderiv ℝ phi x (v p) : ℂ) = 1) :
    |lambda|^n * ‖∫ x, F (p,x) * scalarOscillatoryPhase lambda phi x‖ =
      ‖∫ x, parameterNonstationaryAmplitude A v F n (p,x) * scalarOscillatoryPhase lambda phi x‖ := by
  induction n with
  | zero => simp [parameterNonstationaryAmplitude]
  | succ n ih =>
      have hs := congrArg norm (parameter_nonstationary_step hA hv hF hS hFs n p lambda hphi hrecip)
      simp only [norm_mul, norm_neg, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs] at hs
      rw [pow_succ]
      calc
        _ = |lambda| * (|lambda|^n * ‖∫ x, F (p,x) * scalarOscillatoryPhase lambda phi x‖) := by ring
        _ = _ := by rw [ih, hs]

/-- Uniform arbitrary-power decay for an actual compactly supported
oscillatory integral, with its reciprocal phase derivative supplied smoothly
on a compact parameter family. All integrability hypotheses are derived. -/
theorem uniform_parameter_nonstationary_integral_bound
    {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ} {phi : P → E → ℝ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    {T : Set P} {S : Set E} (hT : IsCompact T) (hS : IsCompact S) (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S)
    (hphi : ∀ p ∈ T, ContDiff ℝ ∞ (phi p))
    (hrecip : ∀ p ∈ T, ∀ x ∈ S, A (p,x) * (fderiv ℝ (phi p) x (v p) : ℂ) = 1)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ lambda : ℝ,
      |lambda|^n * ‖∫ x, F (p,x) * scalarOscillatoryPhase lambda (phi p) x‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := parameterNonstationaryAmplitude_uniform_bound hA hv hF hT hS hFs n
  refine ⟨B * volume.real S + 1, by positivity, fun p hp lambda => ?_⟩
  rw [parameter_nonstationary_iterate_norm hA hv hF hS hFs n p lambda (hphi p hp) (hrecip p hp)]
  have he : (∫ x in S, parameterNonstationaryAmplitude A v F n (p,x) *
      scalarOscillatoryPhase lambda (phi p) x) =
      ∫ x, parameterNonstationaryAmplitude A v F n (p,x) * scalarOscillatoryPhase lambda (phi p) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have hz : parameterNonstationaryAmplitude A v F n (p,x) = 0 := by
        by_contra hn
        exact hx (parameterNonstationaryAmplitude_support hS.isClosed hFs n p hn)
      rw [hz, zero_mul]
  rw [← he]
  have hbound := norm_setIntegral_le_of_norm_le_const_ae (μ := (volume : Measure E))
    hS.measure_lt_top (Eventually.of_forall fun x => show
      ‖parameterNonstationaryAmplitude A v F n (p,x) * scalarOscillatoryPhase lambda (phi p) x‖ ≤ B from by
        simpa only [norm_mul, scalarOscillatoryPhase_norm, mul_one] using hb p hp x)
  exact hbound.trans (le_add_of_nonneg_right zero_le_one)

#print axioms uniform_parameter_nonstationary_integral_bound

end WaringSiegel.WSL3
