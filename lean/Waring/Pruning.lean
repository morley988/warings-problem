import Waring.AdmissibleMinorArc
import Waring.SmoothMomentGrowth

/-!
# Actual pruning estimates with the required strong degree-eight moment

The degree-eight argument uses a full smooth 42nd moment bounded by C*P^34
without a P^epsilon loss. This stronger hypothesis is deliberately stated
explicitly: admissible excess zero alone does not give the pruning conclusion
for an arbitrarily slowly growing arc-width parameter W.

The published ordinary and strong smooth moment estimates remain hypotheses;
the actual mixed Holder bound, exponents, finite constants and little-o pruning
conclusions are proved here.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped ENNReal Topology

namespace Waring.Pruning
open SmoothMoments MixedEndgame AdmissibleMinorArc

/-- The strong full 42nd moment gives the strong full 90th moment by the
actual pointwise bound on the smooth Weyl sum. -/
theorem strong42_to_strong90 {P R Cg : ℝ} (hP : 0 ≤ P)
    (hg : smoothMoment 8 42 P R ≤ Cg*P^34) :
    smoothMoment 8 90 P R ≤ Cg*P^82 := by
  calc
    _ ≤ P^48*smoothMoment 8 42 P R :=
      smoothMoment_order_growth 8 42 90 R (by norm_num) hP
    _ ≤ P^48*(Cg*P^34) := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = Cg*P^82 := by ring

theorem pruning8_exponent_identity {P W Cf Cg : ℝ}
    (hP : 0 < P) (hW : 0 < W) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) :
    (Cf*P^4*W^(-(1/16 : ℝ)))^(2/3 : ℝ) * (Cg*P^82)^(1/3 : ℝ) =
      (Cf^(2/3 : ℝ)*Cg^(1/3 : ℝ))*P^(30 : ℝ)*W^(-(1/24 : ℝ)) := by
  rw [Real.mul_rpow (mul_nonneg hCf (pow_nonneg hP.le _))
      (Real.rpow_nonneg hW.le _),
    Real.mul_rpow hCf (pow_nonneg hP.le _),
    Real.mul_rpow hCg (pow_nonneg hP.le _),
    ← Real.rpow_natCast_mul hP.le, ← Real.rpow_natCast_mul hP.le,
    ← Real.rpow_mul hW.le]
  norm_num
  have hpowers : P^(8/3 : ℝ)*P^(82/3 : ℝ)=P^(30 : ℝ) := by
    rw [← Real.rpow_add hP]
    norm_num
  calc
    _ = (Cf^(2/3 : ℝ)*Cg^(1/3 : ℝ)) *
        (P^(8/3 : ℝ)*P^(82/3 : ℝ))*W^(-(1/24 : ℝ)) := by ring
    _ = _ := by rw [hpowers]; norm_num

/-- The actual degree-eight pruning integral has a strict W-saving. The strong
42nd moment premise is uniform and has exactly the displayed exponent 34. -/
theorem pruning8_abs_bound {P R W Cf Cg : ℝ} (hP : 0 < P) (hW : 0 < W)
    (hCf : 0 < Cf) (hCg : 0 < Cg) (n : ℕ) {A : Set ℝ}
    (hA : A ⊆ Set.Ioc 0 1)
    (hF : ordinaryArcMoment 8 12 P A ≤ ENNReal.ofReal (Cf*P^4*W^(-(1/16 : ℝ))))
    (hg : smoothMoment 8 42 P R ≤ Cg*P^34) :
    |arcContribution 8 8 30 P R n A| ≤
      (Cf^(2/3 : ℝ)*Cg^(1/3 : ℝ))*P^(30 : ℝ)*W^(-(1/24 : ℝ)) := by
  have hg90 : smoothArcMoment 8 90 P R A ≤ ENNReal.ofReal (Cg*P^82) :=
    (smoothArcMoment_le_full 8 90 P R hA).trans
      (ENNReal.ofReal_le_ofReal (strong42_to_strong90 hP.le hg))
  have hFm : AEMeasurable (absoluteOrdinary 8 P) (volume.restrict A) :=
    (continuous_ordinary 8 P).norm.aemeasurable.ennreal_ofReal
  have hgm : AEMeasurable (absoluteSmooth 8 P R) (volume.restrict A) :=
    (continuous_smoothWeyl 8 P R).norm.aemeasurable.ennreal_ofReal
  have hh := Holder.pruning8 hFm hgm
  have hb : ENNReal.ofReal |arcContribution 8 8 30 P R n A| ≤
      ENNReal.ofReal (Cf*P^4*W^(-(1/16 : ℝ)))^(2/3 : ℝ) *
      ENNReal.ofReal (Cg*P^82)^(1/3 : ℝ) :=
    ((arcContribution_abs_le_lintegral 8 8 30 P R n A).trans hh).trans
      (mul_le_mul' (ENNReal.rpow_le_rpow hF (by norm_num))
        (ENNReal.rpow_le_rpow hg90 (by norm_num)))
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity),
    pruning8_exponent_identity hP hW hCf.le hCg.le] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

/-- Degree nine needs only the trivial smooth factor bound in its pruning
region; the ordinary 11th moment supplies the strict W-saving. -/
theorem pruning9_abs_bound {P R W Cf : ℝ} (hP : 0 < P) (hW : 0 < W)
    (hCf : 0 < Cf) (n : ℕ) (A : Set ℝ)
    (hF : ordinaryArcMoment 9 11 P A ≤ ENNReal.ofReal (Cf*P^2*W^(-(1/18 : ℝ)))) :
    |arcContribution 9 11 35 P R n A| ≤ Cf*P^(37 : ℝ)*W^(-(1/18 : ℝ)) := by
  have hpoint (α : ℝ) : absoluteSmooth 9 P R α^35 ≤ ENNReal.ofReal (P^35) := by
    rw [ENNReal.ofReal_pow hP.le]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal (norm_smoothWeyl_le 9 R α hP.le)) _
  have hh : (∫⁻ α, absoluteOrdinary 9 P α^11*absoluteSmooth 9 P R α^35 ∂volume.restrict A) ≤
      ordinaryArcMoment 9 11 P A * ENNReal.ofReal (P^35) := by
    calc
      _ ≤ ∫⁻ α, absoluteOrdinary 9 P α^11*ENNReal.ofReal (P^35) ∂volume.restrict A :=
        lintegral_mono (fun α => mul_le_mul_left' (hpoint α) _)
      _ = _ := lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
  have hb := ((arcContribution_abs_le_lintegral 9 11 35 P R n A).trans hh).trans
    (mul_le_mul_right' hF (ENNReal.ofReal (P^35)))
  rw [← ENNReal.ofReal_mul (by positivity)] at hb
  have hid : (Cf*P^2*W^(-(1/18 : ℝ)))*P^35 = Cf*P^(37 : ℝ)*W^(-(1/18 : ℝ)) := by
    norm_num
    ring
  rw [hid] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb

/-- A strict negative power of any W tending to infinity is enough for a
little-o error relative to an arbitrary main scale. -/
theorem width_saving_isLittleO {ι : Type*} {l : Filter ι}
    {f scale W : ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (hW : Tendsto W l atTop)
    (hbound : f =O[l] (fun n => scale n * W n^(-δ))) :
    f =o[l] scale := by
  have hw : (fun n => W n^(-δ)) =o[l] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr ((tendsto_rpow_neg_atTop hδ).comp hW)
  have hp := (isBigO_refl scale l).mul_isLittleO hw
  exact hbound.trans_isLittleO (by simpa only [mul_one] using hp)

theorem pruning8_isLittleO (P R W : ℕ → ℝ) (A : ℕ → Set ℝ)
    (hP : Tendsto P atTop atTop) (hW : Tendsto W atTop atTop)
    {Cf Cg : ℝ} (hCf : 0 < Cf) (hCg : 0 < Cg)
    (hA : ∀ᶠ n in atTop, A n ⊆ Set.Ioc 0 1)
    (hF : ∀ᶠ n in atTop, ordinaryArcMoment 8 12 (P n) (A n) ≤
      ENNReal.ofReal (Cf*(P n)^4*(W n)^(-(1/16 : ℝ))))
    (hg : ∀ᶠ n in atTop, smoothMoment 8 42 (P n) (R n) ≤ Cg*(P n)^34) :
    (fun n => arcContribution 8 8 30 (P n) (R n) n (A n)) =o[atTop]
      (fun n => (P n)^(30 : ℝ)) := by
  apply width_saving_isLittleO (δ := (1/24 : ℝ)) (by norm_num) hW
  apply IsBigO.of_bound (Cf^(2/3 : ℝ)*Cg^(1/3 : ℝ))
  filter_upwards [hP.eventually_gt_atTop 0,hW.eventually_gt_atTop 0,hA,hF,hg]
    with n hPn hWn hAn hFn hgn
  have hb := pruning8_abs_bound hPn hWn hCf hCg n hAn hFn hgn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (P n)^(30 : ℝ)*(W n)^(-(1/24 : ℝ))), mul_assoc] using hb

theorem pruning9_isLittleO (P R W : ℕ → ℝ) (A : ℕ → Set ℝ)
    (hP : Tendsto P atTop atTop) (hW : Tendsto W atTop atTop)
    {Cf : ℝ} (hCf : 0 < Cf)
    (hF : ∀ᶠ n in atTop, ordinaryArcMoment 9 11 (P n) (A n) ≤
      ENNReal.ofReal (Cf*(P n)^2*(W n)^(-(1/18 : ℝ)))) :
    (fun n => arcContribution 9 11 35 (P n) (R n) n (A n)) =o[atTop]
      (fun n => (P n)^(37 : ℝ)) := by
  apply width_saving_isLittleO (δ := (1/18 : ℝ)) (by norm_num) hW
  apply IsBigO.of_bound Cf
  filter_upwards [hP.eventually_gt_atTop 0,hW.eventually_gt_atTop 0,hF]
    with n hPn hWn hFn
  have hb := pruning9_abs_bound (R := R n) hPn hWn hCf n (A n) hFn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (P n)^(37 : ℝ)*(W n)^(-(1/18 : ℝ))), mul_assoc] using hb

#print axioms pruning8_abs_bound
#print axioms pruning9_abs_bound
#print axioms pruning8_isLittleO
#print axioms pruning9_isLittleO
end Waring.Pruning
