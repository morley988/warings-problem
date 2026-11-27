import WaringSiegel.WSL4ArchComplexSaddle
import WaringSiegel.WSL4ArchComplexFamilyTails
import WaringSiegel.WSL3UnitComplexStationary

/-!
# Complex annular stationary cancellation uniform in a smooth amplitude family

The extra compact parameter remains outside the frequency quantifiers.
This is the uniformity required when dyadic shells rescale a source through zero.
-/
noncomputable section
open MeasureTheory Filter Topology Function Metric
open scoped ContDiff ComplexConjugate BigOperators
namespace WaringSiegel.WSL4
open WSL3
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
set_option maxHeartbeats 1000000

theorem uniform_complex_small_critical_family {F : P × ℂ → ℂ}
    (hF : ContDiff ℝ ∞ F) {T : Set P} (hT : IsCompact T)
    {rho R : ℝ} (hrho : 0 < rho)
    (hFs : ∀ p, support (fun z => F (p,z)) ⊆ complexSourceAnnulus rho R) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ a t : ℂ, ‖a‖ ≤ rho/2 → ‖t‖ = 1 →
      ∀ lambda : ℝ, 0 < lambda →
        lambda*‖∫ z, F (p,z)*scalarOscillatoryPhase lambda (complexSaddlePhase a t) z‖ ≤ C := by
  let U : Set (ℂ × ℂ) := closedBall 0 (rho/2) ×ˢ sphere 0 1
  let G : (P × (ℂ × ℂ)) × ℂ → ℂ := fun q => F (q.1.1,q.2)
  let H : (P × (ℂ × ℂ)) × ℂ → ℂ :=
    fun q => 3*q.1.2.2*q.2^2+(-3*q.1.2.2*q.1.2.1^2)
  have hG : ContDiff ℝ ∞ G := hF.comp
    ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hH : ContDiff ℝ ∞ H := by fun_prop
  have hgap : ∀ p ∈ T ×ˢ U, ∀ z ∈ tsupport (fun y => G (p,y)), rho^2 ≤ ‖H (p,z)‖ := by
    intro p hp z hz
    have ha : ‖p.2.1‖ ≤ rho/2 := by simpa only [mem_closedBall,dist_zero_right] using hp.2.1
    have ht : ‖p.2.2‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hp.2.2
    have hz' := (closure_minimal (hFs p.1) (complexSourceAnnulus_isCompact rho R).isClosed) hz
    have hzr : rho ≤ ‖z‖ := hz'.2
    have he : H (p,z) = 3*p.2.2*(z^2-p.2.1^2) := by dsimp only [H]; ring
    rw [he,norm_mul,norm_mul,ht]
    norm_num
    have htri := norm_sub_le (z^2-p.2.1^2) (-p.2.1^2)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,norm_pow] at htri
    have hza : (rho/2)^2 ≥ ‖p.2.1‖^2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    have hzz := pow_le_pow_left₀ hrho.le hzr 2
    nlinarith
  obtain ⟨C,hC,hb⟩ := uniform_complex_gradient_integral_bound hG hH
    (hT.prod ((isCompact_closedBall 0 (rho/2)).prod (isCompact_sphere 0 1)))
    (complexSourceAnnulus_isCompact rho R) (fun p => hFs p.1)
    (phi := fun p => complexSaddlePhase p.2.1 p.2.2)
    (fun p _ => complexSaddlePhase_contDiff p.2.1 p.2.2)
    (fun p _ z => complex_cubic_gradient_real p.2.2 (-3*p.2.2*p.2.1^2) z)
    (fun p _ z => complex_cubic_gradient_imag p.2.2 (-3*p.2.2*p.2.1^2) z)
    (sq_pos_of_pos hrho) hgap 1
  refine ⟨C,hC,fun p hp a t ha ht lambda hl => ?_⟩
  have hpar : (a,t) ∈ U := by
    constructor
    · simpa only [mem_closedBall,dist_zero_right] using ha
    · simpa only [mem_sphere,dist_zero_right] using ht
  simpa only [pow_one,abs_of_pos hl] using hb (p,(a,t)) ⟨hp,hpar⟩ lambda


/-- Annular cubic decay uniform over an arbitrary fixed compact smooth family. -/
theorem complex_cubic_annular_stationary_family {F : P × ℂ → ℂ}
    (hF : ContDiff ℝ ∞ F) {T : Set P} (hT : IsCompact T)
    (hFnorm : ∀ p ∈ T, ∀ z, ‖F (p,z)‖ ≤ 1)
    {rho R : ℝ} (hrho : 0 < rho) (hR : 0 ≤ R)
    (hFs : ∀ p, support (fun z => F (p,z)) ⊆ complexSourceAnnulus rho R) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ T, ∀ theta u : ℂ,
      (1+‖theta‖)*‖complexCubicOscillatoryIntegral (fun z => F (p,z)) theta u‖ ≤ C := by
  let eta := cubicTailRadius R
  let A := 1+eta⁻¹
  have heta : 0 < eta := cubicTailRadius_pos R
  have hA1 : 1 ≤ A := by
    dsimp only [A]
    linarith [(inv_pos.mpr heta).le]
  have hetaA : 1 ≤ eta*A := by
    dsimp only [A]
    rw [mul_add,mul_one,mul_inv_cancel₀ heta.ne']
    linarith
  have hball : ∀ p, support (fun z => F (p,z)) ⊆ closedBall 0 R := fun p z hz => (hFs p hz).1
  obtain ⟨Cs,hCs,hsmall⟩ := uniform_complex_small_critical_family hF hT hrho hFs
  obtain ⟨Cm,hCm,hmedium⟩ := uniform_complex_saddle_stationary_family (A := A) hF hT hFnorm
    (complexSourceAnnulus_isCompact rho R) hFs (by positivity : 0 < rho/2)
  obtain ⟨Cl,hCl,hlarge⟩ := complex_cubic_nonstationary_family hF hT hR hball 1
  let V := volume.real (closedBall (0:ℂ) R)
  refine ⟨2*(Cs+Cm+Cl+V+1),by dsimp only [V]; positivity,fun p hp theta u => ?_⟩
  let W : ℂ → ℂ := fun z => F (p,z)
  have htriv := complexCubicOscillatoryIntegral_norm_le (hball p) (hFnorm p hp) theta u
  by_cases hsmalltheta : ‖theta‖ ≤ 1
  · have hV : 0 ≤ V := measureReal_nonneg
    change (1+‖theta‖)*‖complexCubicOscillatoryIntegral W theta u‖ ≤ _
    dsimp only [V] at *
    nlinarith [norm_nonneg (complexCubicOscillatoryIntegral W theta u),norm_nonneg theta]
  have ht : 1 < ‖theta‖ := lt_of_not_ge hsmalltheta
  have htheta : theta ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_trans zero_lt_one ht))
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq (-u/(3*theta)) (by norm_num : 0 < (2:ℕ))
  let t := theta/(‖theta‖:ℂ)
  have htt : ‖t‖ = 1 := by
    dsimp only [t]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg theta),
      div_self (norm_ne_zero_iff.mpr htheta)]
  have he := complexCubicOscillatoryIntegral_saddle W htheta ha
  have hmain : ‖theta‖*‖complexCubicOscillatoryIntegral W theta u‖ ≤ Cs+Cm+Cl := by
    by_cases hsa : ‖a‖ ≤ rho/2
    · rw [he]
      have h := hsmall p hp a t hsa htt ‖theta‖ (lt_trans zero_lt_one ht)
      dsimp only [t] at h
      linarith
    by_cases hma : ‖a‖ ≤ A
    · rw [he]
      have h := hmedium p hp a t (le_of_lt (lt_of_not_ge hsa)) hma htt ‖theta‖ (lt_trans zero_lt_one ht)
      dsimp only [t] at h
      linarith
    have haa : A ≤ ‖a‖ := le_of_lt (lt_of_not_ge hma)
    have ha1 : 1 ≤ ‖a‖ := hA1.trans haa
    have hetaa : 1 ≤ eta*‖a‖ := hetaA.trans (mul_le_mul_of_nonneg_left haa heta.le)
    have ha2 : 1 ≤ ‖a‖^2 := by nlinarith
    have hetaa2 : 1 ≤ eta*‖a‖^2 := by
      have hmul := mul_le_mul_of_nonneg_right hetaa (norm_nonneg a)
      nlinarith
    have hu : u = -3*theta*a^2 := by rw [ha]; field_simp
    have hun : ‖u‖ = 3*‖theta‖*‖a‖^2 := by rw [hu,norm_mul,norm_mul,norm_pow]; norm_num
    have hule : ‖theta‖ ≤ ‖u‖ := by rw [hun]; nlinarith
    have hu1 : 1 ≤ ‖u‖ := (le_of_lt ht).trans hule
    have hregion : ‖theta‖ ≤ cubicTailRadius R*‖u‖ := by
      rw [hun]
      change ‖theta‖ ≤ eta*(3*‖theta‖*‖a‖^2)
      have hm := mul_le_mul_of_nonneg_left hetaa2 (norm_nonneg theta)
      nlinarith
    have h := hlarge p hp theta u hu1 hregion
    rw [pow_one] at h
    have hm := mul_le_mul_of_nonneg_right hule (norm_nonneg (complexCubicOscillatoryIntegral W theta u))
    linarith
  have hV : 0 ≤ V := measureReal_nonneg
  dsimp only [V] at *
  nlinarith

#print axioms complex_cubic_annular_stationary_family
end WaringSiegel.WSL4
