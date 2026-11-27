import WaringSiegel.WSL3UnitParametricNonstationary

/-!
# Two-direction nonstationary integration by parts

Two smooth reciprocal-gradient coefficients may be combined to cover a
complex source plane. The reciprocal identity is needed only on the actual
fiber support. This permits parameter-dependent neighborhoods of critical
points to be removed by smooth cutoffs before integration by parts.
-/
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ContDiff
namespace WaringSiegel.WSL3
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1000000

/-- One directional derivative of a smoothly weighted parameter amplitude. -/
def directionalAmplitude (A : P × E → ℂ) (v : P → E) (F : P × E → ℂ) : P × E → ℂ :=
  parameterNonstationaryAmplitude A v F 1

theorem directionalAmplitude_contDiff {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (directionalAmplitude A v F) :=
  parameterNonstationaryAmplitude_contDiff hA hv hF 1

theorem directionalAmplitude_support {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    {S : Set E} (hS : IsClosed S) (p : P) (hF : support (fun x => F (p,x)) ⊆ S) :
    support (fun x => directionalAmplitude A v F (p,x)) ⊆ S := by
  intro x hx
  let g : E → ℂ := fun y => A (p,y)*F (p,y)
  have hgs : support g ⊆ S := fun y hy => hF (mul_ne_zero_iff.mp hy).2
  have hxd : x ∈ support (fderiv ℝ g) := by
    intro hz
    apply hx
    change fderiv ℝ g x (v p) = 0
    rw [hz, ContinuousLinearMap.zero_apply]
  exact (closure_minimal hgs hS) (support_fderiv_subset ℝ hxd)

def gradientAmplitude (A B : P × E → ℂ) (v w : P → E) (F : P × E → ℂ) : ℕ → P × E → ℂ
  | 0 => F
  | n+1 => fun p => directionalAmplitude A v (gradientAmplitude A B v w F n) p +
      directionalAmplitude B w (gradientAmplitude A B v w F n) p

theorem gradientAmplitude_contDiff {A B : P × E → ℂ} {v w : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hv : ContDiff ℝ ∞ v)
    (hw : ContDiff ℝ ∞ w) (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (gradientAmplitude A B v w F n) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
      exact (directionalAmplitude_contDiff hA hv ih).add
        (directionalAmplitude_contDiff hB hw ih)

theorem gradientAmplitude_support {A B : P × E → ℂ} {v w : P → E} {F : P × E → ℂ}
    {S : Set E} (hS : IsClosed S) (p : P) (hF : support (fun x => F (p,x)) ⊆ S) (n : ℕ) :
    support (fun x => gradientAmplitude A B v w F n (p,x)) ⊆ S := by
  induction n with
  | zero => exact hF
  | succ n ih =>
      intro x hx
      by_contra hxn
      have ha : directionalAmplitude A v (gradientAmplitude A B v w F n) (p,x) = 0 := by
        by_contra hn
        exact hxn (directionalAmplitude_support hS p ih hn)
      have hb : directionalAmplitude B w (gradientAmplitude A B v w F n) (p,x) = 0 := by
        by_contra hn
        exact hxn (directionalAmplitude_support hS p ih hn)
      exact hx (by simp only [gradientAmplitude,ha,hb,zero_add])

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- A compact fiber is sufficient for the exact directional integration by parts. -/
theorem directionalAmplitude_integral {A : P × E → ℂ} {v : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    {S : Set E} (hS : IsCompact S) (p : P) (hFs : support (fun x => F (p,x)) ⊆ S)
    (lambda : ℝ) {phi : E → ℝ} (hphi : ContDiff ℝ ∞ phi) :
    (∫ x, (A (p,x)*F (p,x))*fderiv ℝ (scalarOscillatoryPhase lambda phi) x (v p)) =
      -(∫ x, directionalAmplitude A v F (p,x)*scalarOscillatoryPhase lambda phi x) := by
  let g : E → ℂ := fun x => A (p,x)*F (p,x)
  have hg : ContDiff ℝ ∞ g := (hA.mul hF).comp (contDiff_const.prodMk contDiff_id)
  have hgc : HasCompactSupport g :=
    (HasCompactSupport.of_support_subset_isCompact hS hFs).mul_left
  have ht : Continuous (fun x => directionalAmplitude A v F (p,x)) :=
    (directionalAmplitude_contDiff hA hv hF).continuous.comp (continuous_const.prodMk continuous_id)
  have htc : HasCompactSupport (fun x => directionalAmplitude A v F (p,x)) :=
    HasCompactSupport.of_support_subset_isCompact hS (directionalAmplitude_support hS.isClosed p hFs)
  have hphase := scalarOscillatoryPhase_contDiff lambda hphi
  have hpd : Continuous (fun x => fderiv ℝ (scalarOscillatoryPhase lambda phi) x (v p)) :=
    (hphase.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((ht.mul hphase.continuous).integrable_of_hasCompactSupport htc.mul_right)
    ((hg.continuous.mul hpd).integrable_of_hasCompactSupport hgc.mul_right)
    ((hg.continuous.mul hphase.continuous).integrable_of_hasCompactSupport hgc.mul_right)
    (hg.differentiable (by simp)) (hphase.differentiable (by simp))

/-- The two directional derivatives combine through the reciprocal-gradient identity. -/
theorem gradient_nonstationary_step {A B : P × E → ℂ} {v w : P → E} {F : P × E → ℂ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hv : ContDiff ℝ ∞ v)
    (hw : ContDiff ℝ ∞ w) (hF : ContDiff ℝ ∞ F)
    {S : Set E} (hS : IsCompact S) (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S)
    (n : ℕ) (p : P) (lambda : ℝ) {phi : E → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hrecip : ∀ x ∈ tsupport (fun y => F (p,y)),
      A (p,x)*(fderiv ℝ phi x (v p) : ℂ) + B (p,x)*(fderiv ℝ phi x (w p) : ℂ) = 1) :
    ((lambda:ℂ)*Complex.I)*(∫ x, gradientAmplitude A B v w F n (p,x)*scalarOscillatoryPhase lambda phi x) =
      -(∫ x, gradientAmplitude A B v w F (n+1) (p,x)*scalarOscillatoryPhase lambda phi x) := by
  let G := gradientAmplitude A B v w F n
  have hG : ContDiff ℝ ∞ G := gradientAmplitude_contDiff hA hB hv hw hF n
  have hGs : support (fun x => G (p,x)) ⊆ S := gradientAmplitude_support hS.isClosed p (hFs p) n
  have hGt : support (fun x => G (p,x)) ⊆ tsupport (fun y => F (p,y)) :=
    gradientAmplitude_support isClosed_closure p subset_closure n
  let phase := scalarOscillatoryPhase lambda phi
  have hphase : ContDiff ℝ ∞ phase := scalarOscillatoryPhase_contDiff lambda hphi
  have hgc : HasCompactSupport (fun x => G (p,x)) := HasCompactSupport.of_support_subset_isCompact hS hGs
  have hcont : Continuous (fun x => G (p,x)) := hG.continuous.comp (continuous_const.prodMk continuous_id)
  have hInt (A' : P × E → ℂ) (v' : P → E) (hA' : ContDiff ℝ ∞ A') (hv' : ContDiff ℝ ∞ v') :
      Integrable (fun x => (A' (p,x)*G (p,x))*fderiv ℝ phase x (v' p)) := by
    have hcA : Continuous (fun x => A' (p,x)) := hA'.continuous.comp (continuous_const.prodMk continuous_id)
    have hd : Continuous (fun x => fderiv ℝ phase x (v' p)) :=
      (hphase.fderiv_right (m := ∞) (by simp)).continuous.clm_apply continuous_const
    exact ((hcA.mul hcont).mul hd).integrable_of_hasCompactSupport hgc.mul_left.mul_right
  have hTerm (A' : P × E → ℂ) (v' : P → E) (hA' : ContDiff ℝ ∞ A') (hv' : ContDiff ℝ ∞ v') :
      Integrable (fun x => directionalAmplitude A' v' G (p,x)*phase x) := by
    have hc : Continuous (fun x => directionalAmplitude A' v' G (p,x)) :=
      (directionalAmplitude_contDiff hA' hv' hG).continuous.comp (continuous_const.prodMk continuous_id)
    have hcs : HasCompactSupport (fun x => directionalAmplitude A' v' G (p,x)) :=
      HasCompactSupport.of_support_subset_isCompact hS (directionalAmplitude_support hS.isClosed p hGs)
    exact (hc.mul hphase.continuous).integrable_of_hasCompactSupport hcs.mul_right
  have he (x : E) : ((lambda:ℂ)*Complex.I)*(G (p,x)*phase x) =
      (A (p,x)*G (p,x))*fderiv ℝ phase x (v p) +
      (B (p,x)*G (p,x))*fderiv ℝ phase x (w p) := by
    simp only [phase, scalarOscillatoryPhase_fderiv lambda (hphi.differentiable (by simp))]
    by_cases hx : x ∈ tsupport (fun y => F (p,y))
    · have hr := hrecip x hx
      calc
        _ = ((lambda:ℂ)*Complex.I)*(G (p,x)*scalarOscillatoryPhase lambda phi x)*
            (A (p,x)*(fderiv ℝ phi x (v p):ℂ)+B (p,x)*(fderiv ℝ phi x (w p):ℂ)) := by rw [hr,mul_one]
        _ = _ := by ring
    · have hz : G (p,x) = 0 := by by_contra hn; exact hx (hGt hn)
      simp only [hz,zero_mul,mul_zero,zero_add]
  calc
    _ = ∫ x, ((lambda:ℂ)*Complex.I)*(G (p,x)*phase x) := (integral_const_mul _ _).symm
    _ = ∫ x, ((A (p,x)*G (p,x))*fderiv ℝ phase x (v p) +
        (B (p,x)*G (p,x))*fderiv ℝ phase x (w p)) := integral_congr_ae (Eventually.of_forall he)
    _ = _ := by
      rw [integral_add (hInt A v hA hv) (hInt B w hB hw),
        directionalAmplitude_integral hA hv hG hS p hGs lambda hphi,
        directionalAmplitude_integral hB hw hG hS p hGs lambda hphi]
      change -(∫ x, directionalAmplitude A v G (p,x)*phase x) +
        -(∫ x, directionalAmplitude B w G (p,x)*phase x) =
        -(∫ x, (directionalAmplitude A v G (p,x)+directionalAmplitude B w G (p,x))*phase x)
      simp_rw [add_mul]
      rw [integral_add (hTerm A v hA hv) (hTerm B w hB hw)]
      ring

/-- Uniform arbitrary-power decay using two reciprocal-gradient components. -/
theorem uniform_gradient_nonstationary_integral_bound
    {A B : P × E → ℂ} {v w : P → E} {F : P × E → ℂ} {phi : P → E → ℝ}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) (hv : ContDiff ℝ ∞ v)
    (hw : ContDiff ℝ ∞ w) (hF : ContDiff ℝ ∞ F)
    {T : Set P} {S : Set E} (hT : IsCompact T) (hS : IsCompact S)
    (hFs : ∀ p, support (fun x => F (p,x)) ⊆ S)
    (hphi : ∀ p ∈ T, ContDiff ℝ ∞ (phi p))
    (hrecip : ∀ p ∈ T, ∀ x ∈ tsupport (fun y => F (p,y)),
      A (p,x)*(fderiv ℝ (phi p) x (v p):ℂ)+B (p,x)*(fderiv ℝ (phi p) x (w p):ℂ)=1)
    (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ lambda : ℝ,
      |lambda|^n * ‖∫ x, F (p,x)*scalarOscillatoryPhase lambda (phi p) x‖ ≤ C := by
  have hGn := gradientAmplitude_contDiff hA hB hv hw hF n
  obtain ⟨M,hM,hm⟩ := ((hT.prod hS).image hGn.continuous).isBounded.exists_pos_norm_le
  refine ⟨M*volume.real S+1,by positivity,fun p hp lambda => ?_⟩
  have hnorm (m : ℕ) : |lambda|^m*‖∫ x, F (p,x)*scalarOscillatoryPhase lambda (phi p) x‖ =
      ‖∫ x, gradientAmplitude A B v w F m (p,x)*scalarOscillatoryPhase lambda (phi p) x‖ := by
    induction m with
    | zero => simp [gradientAmplitude]
    | succ m ih =>
        have hs := congrArg norm (gradient_nonstationary_step hA hB hv hw hF hS hFs
          m p lambda (hphi p hp) (hrecip p hp))
        simp only [norm_mul,norm_neg,Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs] at hs
        rw [pow_succ]
        calc
          _ = |lambda| * (|lambda|^m*‖∫ x, F (p,x)*scalarOscillatoryPhase lambda (phi p) x‖) := by ring
          _ = _ := by rw [ih,hs]
  rw [hnorm n]
  have hsupport : support (fun x => gradientAmplitude A B v w F n (p,x)) ⊆ S :=
    gradientAmplitude_support hS.isClosed p (hFs p) n
  have he : (∫ x in S, gradientAmplitude A B v w F n (p,x)*scalarOscillatoryPhase lambda (phi p) x) =
      ∫ x, gradientAmplitude A B v w F n (p,x)*scalarOscillatoryPhase lambda (phi p) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have hz : gradientAmplitude A B v w F n (p,x) = 0 := by by_contra hn; exact hx (hsupport hn)
      rw [hz,zero_mul]
  rw [← he]
  have hbound := norm_setIntegral_le_of_norm_le_const_ae' (μ := (volume : Measure E)) hS.measure_lt_top
    (Eventually.of_forall fun x hx => show
      ‖gradientAmplitude A B v w F n (p,x)*scalarOscillatoryPhase lambda (phi p) x‖ ≤ M from by
        rw [norm_mul,scalarOscillatoryPhase_norm,mul_one]
        exact hm _ (Set.mem_image_of_mem _ ⟨hp,hx⟩))
  exact hbound.trans (le_add_of_nonneg_right zero_le_one)

#print axioms uniform_gradient_nonstationary_integral_bound
end WaringSiegel.WSL3
