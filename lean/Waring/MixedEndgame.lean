import Waring.MixedRepresentation
import Waring.MinorArcFinite
import Waring.AsymptoticEndgame
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Composed conditional endgames for the actual mixed representation integral

A measurable three-part partition supplies the exact decomposition. The minor
contribution is dominated by the actual absolute mixed moment; finite uniform
moment estimates produce a strict power saving and therefore little-o of the
main scale. Positive main terms and little-o pruning then imply the actual
Waring bounds. The required number-theoretic estimates remain explicit premises.
-/

noncomputable section
open Filter Asymptotics MeasureTheory
open scoped ENNReal Topology

namespace Waring.MixedEndgame
open Waring.SmoothMoments

/-- The complex integrand whose coefficient is the mixed representation count. -/
def integrand (k u v : ℕ) (P R : ℝ) (n : ℕ) (α : ℝ) : ℂ :=
  ordinaryWeyl k P α ^ u * smoothWeyl k P R α ^ v *
    fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))

def arcContribution (k u v : ℕ) (P R : ℝ) (n : ℕ) (A : Set ℝ) : ℝ :=
  (∫ α in A, integrand k u v P R n α).re

def absoluteOrdinary (k : ℕ) (P α : ℝ) : ℝ≥0∞ := ENNReal.ofReal ‖ordinaryWeyl k P α‖
def absoluteSmooth (k : ℕ) (P R α : ℝ) : ℝ≥0∞ := ENNReal.ofReal ‖smoothWeyl k P R α‖

def ordinaryArcMoment (k p : ℕ) (P : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ α, absoluteOrdinary k P α ^ p ∂volume.restrict A

def smoothArcMoment (k p : ℕ) (P R : ℝ) (A : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ α, absoluteSmooth k P R α ^ p ∂volume.restrict A

theorem continuous_ordinary (k : ℕ) (P : ℝ) : Continuous (ordinaryWeyl k P) := by
  unfold ordinaryWeyl
  exact continuous_finset_sum _ (fun n _ => continuous_phase k n)

theorem continuous_integrand (k u v : ℕ) (P R : ℝ) (n : ℕ) :
    Continuous (integrand k u v P R n) :=
  (((continuous_ordinary k P).pow u).mul ((continuous_smoothWeyl k P R).pow v)).mul
    ((fourier (-(n : ℤ))).continuous.comp (AddCircle.continuous_mk' 1))

/-- A genuine measurable partition of one integration period. -/
structure ArcPartition (core pruning minor : Set ℝ) : Prop where
  measurableCore : MeasurableSet core
  measurablePruning : MeasurableSet pruning
  measurableMinor : MeasurableSet minor
  corePruning : Disjoint core pruning
  coreMinor : Disjoint core minor
  pruningMinor : Disjoint pruning minor
  cover : core ∪ (pruning ∪ minor) = Set.Ioc 0 1

/-- Exact decomposition of the actual mixed integral under the stated partition. -/
theorem mixedIntegral_partition (k u v : ℕ) (P R : ℝ) (n : ℕ)
    {core pruning minor : Set ℝ} (h : ArcPartition core pruning minor) :
    (mixedRepresentationIntegral k u v P R n).re =
      arcContribution k u v P R n core +
        (arcContribution k u v P R n pruning + arcContribution k u v P R n minor) := by
  have hi : IntegrableOn (integrand k u v P R n) (Set.Ioc 0 1) :=
    ((continuous_integrand k u v P R n).intervalIntegrable 0 1).1
  have hsubA : core ⊆ Set.Ioc 0 1 := by rw [← h.cover]; exact Set.subset_union_left
  have hsubBC : pruning ∪ minor ⊆ Set.Ioc 0 1 := by rw [← h.cover]; exact Set.subset_union_right
  have hsubB : pruning ⊆ Set.Ioc 0 1 := Set.subset_union_left.trans hsubBC
  have hsubC : minor ⊆ Set.Ioc 0 1 := Set.subset_union_right.trans hsubBC
  change (∫ α in (0 : ℝ)..1, integrand k u v P R n α).re = _
  rw [intervalIntegral.integral_of_le zero_le_one, ← h.cover,
    setIntegral_union (h.corePruning.union_right h.coreMinor)
      (h.measurablePruning.union h.measurableMinor) (hi.mono_set hsubA) (hi.mono_set hsubBC),
    setIntegral_union h.pruningMinor h.measurableMinor (hi.mono_set hsubB) (hi.mono_set hsubC),
    Complex.add_re, Complex.add_re]
  rfl

/-- The norm of the twisting character is exactly one. -/
theorem integrand_norm (k u v : ℕ) (P R : ℝ) (n : ℕ) (α : ℝ) :
    ‖integrand k u v P R n α‖ = ‖ordinaryWeyl k P α‖ ^ u * ‖smoothWeyl k P R α‖ ^ v := by
  have hchar : ‖fourier (-(n : ℤ)) (α : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
  simp only [integrand, norm_mul, norm_pow, hchar, mul_one]

/-- The actual signed arc contribution is dominated by its absolute mixed moment. -/
theorem arcContribution_abs_le_lintegral (k u v : ℕ) (P R : ℝ) (n : ℕ) (A : Set ℝ) :
    ENNReal.ofReal |arcContribution k u v P R n A| ≤
      ∫⁻ α, absoluteOrdinary k P α ^ u * absoluteSmooth k P R α ^ v ∂volume.restrict A := by
  have h := (Complex.abs_re_le_norm (∫ α in A, integrand k u v P R n α)).trans
    (norm_integral_le_lintegral_norm (μ := volume.restrict A) (integrand k u v P R n))
  have h' := ENNReal.ofReal_le_of_le_toReal h
  simpa only [arcContribution,integrand_norm,ENNReal.ofReal_mul (pow_nonneg (norm_nonneg _) _),
    ENNReal.ofReal_pow (norm_nonneg _),absoluteOrdinary,absoluteSmooth] using h'

/-- A positive core and two negligible errors imply the actual mixed Waring conclusion. -/
theorem waringBound_of_mixed_two_errors {k u v : ℕ} (P R : ℕ → ℝ)
    {main pruning minor scale : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hscale : ∀ᶠ n in atTop, 0 < scale n)
    (hdecomp : ∀ᶠ n in atTop, (mixedRepresentationIntegral k u v (P n) (R n) n).re =
      main n + (pruning n + minor n))
    (hmain : ∀ᶠ n in atTop, c*scale n ≤ main n)
    (hpruning : pruning =o[atTop] scale) (hminor : minor =o[atTop] scale) :
    WaringBound k (u+v) := by
  have he := (hpruning.add hminor).def (half_pos hc)
  have hpos : ∀ᶠ n in atTop, 0 < (mixedRepresentationIntegral k u v (P n) (R n) n).re := by
    filter_upwards [hscale,hdecomp,hmain,he] with n hs hd hm herr
    have hb : |pruning n+minor n| ≤ c*scale n/2 := by
      simpa only [Real.norm_eq_abs,abs_of_pos hs,div_mul_eq_mul_div] using herr
    have hn := neg_abs_le (pruning n+minor n)
    have hcscale := mul_pos hc hs
    linarith
  exact waringBound_of_eventually_mixed_integral_pos P R (eventually_atTop.mp hpos)

/-- Actual ordinary/smooth moment hypotheses at one degree-eight minor-arc scale. -/
def MinorInputs8 (P R : ℝ) (A : Set ℝ) (C₀ C₁ C₂ : ℝ≥0∞) (ε : ℝ) : Prop :=
  ordinaryArcMoment 8 72 P A ≤ C₀*ENNReal.ofReal P ^ (63+ε) ∧
  smoothArcMoment 8 32 P R A ≤ C₁*ENNReal.ofReal P ^ (24+Endgame.delta8_32+ε) ∧
  smoothArcMoment 8 34 P R A ≤ C₂*ENNReal.ofReal P ^ (26+Endgame.delta8_34+ε)

def MinorInputs9 (P R : ℝ) (A : Set ℝ) (C₀ C₁ C₂ : ℝ≥0∞) (ε : ℝ) : Prop :=
  ordinaryArcMoment 9 90 P A ≤ C₀*ENNReal.ofReal P ^ (80+ε) ∧
  smoothArcMoment 9 38 P R A ≤ C₁*ENNReal.ofReal P ^ (29+Endgame.delta9_38+ε) ∧
  smoothArcMoment 9 40 P R A ≤ C₂*ENNReal.ofReal P ^ (31+Endgame.delta9_40+ε)

/-- Convert an ENNReal power estimate with a positive real constant into the
ordinary real estimate needed by asymptotics. -/
theorem real_power_bound {x C P exponent : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P)
    (he : 0 ≤ exponent)
    (h : ENNReal.ofReal |x| ≤ ENNReal.ofReal C * ENNReal.ofReal P ^ exponent) :
    |x| ≤ C*P^exponent := by
  rw [ENNReal.ofReal_rpow_of_nonneg hP he, ← ENNReal.ofReal_mul hC] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (Real.rpow_nonneg hP _))).mp h

/-- The three finite degree-eight moments produce a uniform real bound for the
actual signed minor-arc contribution. -/
theorem minor8_abs_bound {P R : ℝ} (hP : 1 ≤ P) (n : ℕ) (A : Set ℝ)
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤) (hC₂ : C₂ ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 7/200000) (h : MinorInputs8 P R A C₀ C₁ C₂ ε) :
    |arcContribution 8 8 30 P R n A| ≤
      MinorArcFinite.positiveConstant8 C₀ C₁ C₂ * P^(30-7/200000 : ℝ) := by
  have hP' : 1 ≤ ENNReal.ofReal P := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hP
  have hF : AEMeasurable (absoluteOrdinary 8 P) (volume.restrict A) :=
    (continuous_ordinary 8 P).norm.aemeasurable.ennreal_ofReal
  have hg : AEMeasurable (absoluteSmooth 8 P R) (volume.restrict A) :=
    (continuous_smoothWeyl 8 P R).norm.aemeasurable.ennreal_ofReal
  have hb := MinorArcFinite.degree8 hF hg hP' ENNReal.ofReal_ne_top
    hC₀ hC₁ hC₂ hε h.1 h.2.1 h.2.2
  exact real_power_bound (MinorArcFinite.positiveConstant8_pos _ _ _).le
    (zero_le_one.trans hP) (by norm_num)
    ((arcContribution_abs_le_lintegral 8 8 30 P R n A).trans hb.2.1)

theorem minor9_abs_bound {P R : ℝ} (hP : 1 ≤ P) (n : ℕ) (A : Set ℝ)
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤) (hC₂ : C₂ ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 1/4000) (h : MinorInputs9 P R A C₀ C₁ C₂ ε) :
    |arcContribution 9 11 35 P R n A| ≤
      MinorArcFinite.positiveConstant9 C₀ C₁ C₂ * P^(37-1/4000 : ℝ) := by
  have hP' : 1 ≤ ENNReal.ofReal P := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hP
  have hF : AEMeasurable (absoluteOrdinary 9 P) (volume.restrict A) :=
    (continuous_ordinary 9 P).norm.aemeasurable.ennreal_ofReal
  have hg : AEMeasurable (absoluteSmooth 9 P R) (volume.restrict A) :=
    (continuous_smoothWeyl 9 P R).norm.aemeasurable.ennreal_ofReal
  have hb := MinorArcFinite.degree9 hF hg hP' ENNReal.ofReal_ne_top
    hC₀ hC₁ hC₂ hε h.1 h.2.1 h.2.2
  exact real_power_bound (MinorArcFinite.positiveConstant9_pos _ _ _).le
    (zero_le_one.trans hP) (by norm_num)
    ((arcContribution_abs_le_lintegral 9 11 35 P R n A).trans hb.2.1)

/-- Finite uniform moment constants yield a little-o degree-eight minor error
along any length function tending to infinity. -/
theorem minor8_isLittleO (P R : ℕ → ℝ) (A : ℕ → Set ℝ)
    (hP : Tendsto P atTop atTop)
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤) (hC₂ : C₂ ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 7/200000)
    (h : ∀ᶠ n in atTop, MinorInputs8 (P n) (R n) (A n) C₀ C₁ C₂ ε) :
    (fun n => arcContribution 8 8 30 (P n) (R n) n (A n)) =o[atTop]
      (fun n => P n ^ (30 : ℝ)) := by
  apply AsymptoticEndgame.power_saving_isLittleO (saving := (7/200000 : ℝ)) (by norm_num) hP
  apply IsBigO.of_bound (MinorArcFinite.positiveConstant8 C₀ C₁ C₂)
  filter_upwards [hP.eventually_ge_atTop 1,h] with n hPn hn
  have hb := minor8_abs_bound hPn n (A n) hC₀ hC₁ hC₂ hε hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hPn) _)] using hb

theorem minor9_isLittleO (P R : ℕ → ℝ) (A : ℕ → Set ℝ)
    (hP : Tendsto P atTop atTop)
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤) (hC₂ : C₂ ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 1/4000)
    (h : ∀ᶠ n in atTop, MinorInputs9 (P n) (R n) (A n) C₀ C₁ C₂ ε) :
    (fun n => arcContribution 9 11 35 (P n) (R n) n (A n)) =o[atTop]
      (fun n => P n ^ (37 : ℝ)) := by
  apply AsymptoticEndgame.power_saving_isLittleO (saving := (1/4000 : ℝ)) (by norm_num) hP
  apply IsBigO.of_bound (MinorArcFinite.positiveConstant9 C₀ C₁ C₂)
  filter_upwards [hP.eventually_ge_atTop 1,h] with n hPn hn
  have hb := minor9_abs_bound hPn n (A n) hC₀ hC₁ hC₂ hε hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hPn) _)] using hb

/-- A genuinely composed conditional G(8) conclusion. The missing analytic
premises are the three displayed moment estimates, the positive narrow-core
main term, and the negligible pruning contribution. The minor little-o bound
and the passage to positive natural representations are proved here. -/
theorem waring8_conditional (P R : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ)
    (hP : Tendsto P atTop atTop)
    (hpartition : ∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n))
    {c : ℝ} (hc : 0 < c)
    (hcore : ∀ᶠ n in atTop,
      c * P n ^ (30 : ℝ) ≤ arcContribution 8 8 30 (P n) (R n) n (core n))
    (hpruning : (fun n => arcContribution 8 8 30 (P n) (R n) n (pruning n)) =o[atTop]
      (fun n => P n ^ (30 : ℝ)))
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤) (hC₂ : C₂ ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 7/200000)
    (hmoments : ∀ᶠ n in atTop, MinorInputs8 (P n) (R n) (minor n) C₀ C₁ C₂ ε) :
    WaringBound 8 38 := by
  have hscale : ∀ᶠ n in atTop, 0 < P n ^ (30 : ℝ) := by
    filter_upwards [hP.eventually_ge_atTop 1] with n hn
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hn) _
  have hd := hpartition.mono (fun n hn => mixedIntegral_partition 8 8 30 (P n) (R n) n hn)
  exact waringBound_of_mixed_two_errors (k := 8) (u := 8) (v := 30) P R hc hscale hd hcore
    hpruning (minor8_isLittleO P R minor hP hC₀ hC₁ hC₂ hε hmoments)

/-- The analogous composed conditional G(9) conclusion uses eleven ordinary
and thirty-five smooth variables. No Waring conclusion is among its premises. -/
theorem waring9_conditional (P R : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ)
    (hP : Tendsto P atTop atTop)
    (hpartition : ∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n))
    {c : ℝ} (hc : 0 < c)
    (hcore : ∀ᶠ n in atTop,
      c * P n ^ (37 : ℝ) ≤ arcContribution 9 11 35 (P n) (R n) n (core n))
    (hpruning : (fun n => arcContribution 9 11 35 (P n) (R n) n (pruning n)) =o[atTop]
      (fun n => P n ^ (37 : ℝ)))
    {C₀ C₁ C₂ : ℝ≥0∞} (hC₀ : C₀ ≠ ⊤) (hC₁ : C₁ ≠ ⊤) (hC₂ : C₂ ≠ ⊤)
    {ε : ℝ} (hε : ε ≤ 1/4000)
    (hmoments : ∀ᶠ n in atTop, MinorInputs9 (P n) (R n) (minor n) C₀ C₁ C₂ ε) :
    WaringBound 9 46 := by
  have hscale : ∀ᶠ n in atTop, 0 < P n ^ (37 : ℝ) := by
    filter_upwards [hP.eventually_ge_atTop 1] with n hn
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hn) _
  have hd := hpartition.mono (fun n hn => mixedIntegral_partition 9 11 35 (P n) (R n) n hn)
  exact waringBound_of_mixed_two_errors (k := 9) (u := 11) (v := 35) P R hc hscale hd hcore
    hpruning (minor9_isLittleO P R minor hP hC₀ hC₁ hC₂ hε hmoments)

#print axioms mixedIntegral_partition
#print axioms minor8_isLittleO
#print axioms minor9_isLittleO
#print axioms waring8_conditional
#print axioms waring9_conditional
end Waring.MixedEndgame
