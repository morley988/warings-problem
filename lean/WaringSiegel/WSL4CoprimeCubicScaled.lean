import WaringSiegel.WSL4CoprimeCubicWeyl
import WaringSiegel.WSL4ArchNonzeroFourth

/-! # Prime-uniform cubic minor bounds for an arbitrary fixed compact root box -/
noncomputable section
set_option maxHeartbeats 1300000
open MeasureTheory Module NumberField NumberField.mixedEmbedding
open scoped NumberField BigOperators Classical ContDiff
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem compactCoprimeTraceCubicSum_scaled_weight (w : mixedSpace K→ℂ)
    (T P : ℝ) (hT : T≠0) (p : ℕ) (q r : ArchimedeanTraceTorus K) :
    compactCoprimeTraceCubicSum (fun x => w (T • x)) (T*P) p q r =
      compactCoprimeTraceCubicSum w P p q r := by
  unfold compactCoprimeTraceCubicSum
  apply tsum_congr
  intro x
  dsimp only
  rw [smul_smul]
  have he : T*(T*P)⁻¹=P⁻¹ := by rw [mul_inv_rev]; field_simp
  rw [he]

theorem compactCoprimeTraceCubicSum_compact_minor_fourth_bound
    {w : mixedSpace K→ℂ} (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (T : ℝ) (hT : 1≤T) (hsupport : ∀x,w x≠0 → ‖x‖≤T)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ), 1≤P → ∀p:ℕ,p.Prime →
      ∀q r:ArchimedeanTraceTorus K,
      q∉traceMajorArcUnion (P^3) ((6*T)^finrank ℚ K*P^finrank ℚ K) →
      ‖compactCoprimeTraceCubicSum w P p q r‖^4≤C*(P^finrank ℚ K)^3*P^ε := by
  have hT0 : 0<T := by linarith
  let v : mixedSpace K→ℂ := fun x => w (T • x)
  have hv : ContDiff ℝ ∞ v := hw.comp (contDiff_const.smul contDiff_id)
  have hvc : HasCompactSupport v := hc.comp_smul hT0.ne'
  have hvs : ∀x,v x≠0 → ‖x‖≤1 := by
    intro x hx
    have hh := hsupport (T • x) hx
    rw [_root_.norm_smul,Real.norm_eq_abs,abs_of_pos hT0] at hh
    nlinarith
  obtain ⟨C,hC,hbound⟩ := compactCoprimeTraceCubicSum_minor_fourth_bound hv hvc hvs hε
  refine ⟨C*(T^finrank ℚ K)^3*T^ε,by positivity,?_⟩
  intro P hP p hp q r hminor
  have hP0 : 0<P := by linarith
  have hTP : 1≤T*P := one_le_mul_of_one_le_of_one_le hT hP
  have hscale : P^3≤(T*P)^2*(4*(T*P)) := by
    have hh : P^3≤(T*P)^3 := pow_le_pow_left₀ hP0.le
      (le_mul_of_one_le_left hP0.le hT) 3
    nlinarith [pow_nonneg (mul_nonneg hT0.le hP0.le) 3]
  have hm : q∉traceMajorArcUnion ((T*P)^2*(4*(T*P)))
      ((6:ℝ)^finrank ℚ K*(T*P)^finrank ℚ K) := by
    intro hq
    apply hminor
    have hh := traceMajorArcUnion_antitone_scale hscale hq
    simpa only [mul_pow,mul_assoc] using hh
  have hb := hbound (T*P) hTP p hp q r hm
  dsimp only [v] at hb
  rw [compactCoprimeTraceCubicSum_scaled_weight w T P hT0.ne'] at hb
  apply hb.trans_eq
  rw [mul_pow,mul_pow,Real.mul_rpow hT0.le hP0.le]
  ring

#print axioms compactCoprimeTraceCubicSum_compact_minor_fourth_bound
end WaringSiegel.WSL4Local
