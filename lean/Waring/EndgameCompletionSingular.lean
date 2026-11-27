import Waring.EndgameCompletionMajor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Explicit decay of the ordinary monomial integral

The decay estimates here concern the actual oscillatory integral used in
`ordinary_rational_approximation`. They follow from integration by parts,
without an assumed oscillatory-integral estimate.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Waring.EndgameCompletion
open QuadraticModulation

/-- Exact scale normalization, including a zero cutoff. -/
theorem monomialIntegral_scale (k : ℕ) (P β : ℝ) :
    monomialIntegral k P β = (P : ℂ)*monomialIntegral k 1 (β*P^k) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (fun t : ℝ => e (β*t^k)) (a := 0) (b := 1) P
  simpa only [mul_zero, mul_one, mul_pow, mul_assoc, monomialIntegral,
    Complex.real_smul, Complex.ofReal_mul] using h.symm

/-- A first-derivative bound with an explicit reciprocal derivative.
The real factor `g` is nonnegative at the endpoints and has nonpositive
derivative. This form makes the cancellation in the error integral exact. -/
theorem norm_integral_le_two_mul_of_reciprocal_deriv
    {a b : ℝ} (hab : a ≤ b) {f f' : ℝ → ℂ} {g g' : ℝ → ℝ} (C : ℂ)
    (hfc : ContinuousOn f (Set.Icc a b))
    (hf'c : ContinuousOn f' (Set.Icc a b))
    (hgc : ContinuousOn g (Set.Icc a b))
    (hg'c : ContinuousOn g' (Set.Icc a b))
    (hfd : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hgd : ∀ t ∈ Set.Icc a b, HasDerivAt g (g' t) t)
    (hident : ∀ t ∈ Set.Icc a b, C*(g t : ℂ)*f' t = f t)
    (hfnorm : ∀ t ∈ Set.Icc a b, ‖f t‖ ≤ 1)
    (hga : 0 ≤ g a) (hgb : 0 ≤ g b)
    (hgneg : ∀ t ∈ Set.Icc a b, g' t ≤ 0) :
    ‖∫ t in a..b, f t‖ ≤ 2*‖C‖*g a := by
  have hfc' : ContinuousOn f (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hf'c' : ContinuousOn f' (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hgc' : ContinuousOn g (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hg'c' : ContinuousOn g' (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hCgc : ContinuousOn (fun t => C*(g t : ℂ)) (Set.uIcc a b) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hgc')
  have hCg'c : ContinuousOn (fun t => C*(g' t : ℂ)) (Set.uIcc a b) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hg'c')
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t => C*(g t : ℂ)) (u' := fun t => C*(g' t : ℂ))
    (v := f) (v' := f') hCgc hfc'
    (fun t ht => (hgd t (by simpa only [min_eq_left hab, max_eq_right hab] using
      Set.Ioo_subset_Icc_self ht)).ofReal_comp.const_mul C)
    (fun t ht => hfd t (by simpa only [min_eq_left hab, max_eq_right hab] using
      Set.Ioo_subset_Icc_self ht))
    hCg'c.intervalIntegrable hf'c'.intervalIntegrable
  have hid : (∫ t in a..b, C*(g t : ℂ)*f' t) = ∫ t in a..b, f t := by
    apply intervalIntegral.integral_congr
    simpa only [Set.uIcc_of_le hab] using hident
  rw [hid] at hibp
  have hFTC : (∫ t in a..b, g' t) = g b-g a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hg'c'.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hgd
  have hint : ‖∫ t in a..b, C*(g' t : ℂ)*f t‖ ≤ ‖C‖*(g a-g b) := by
    calc
      _ ≤ ∫ t in a..b, ‖C*(g' t : ℂ)*f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ t in a..b, ‖C‖*(-g' t) := by
        apply intervalIntegral.integral_mono_on hab
          ((hCg'c.mul hfc').norm.intervalIntegrable)
          ((continuousOn_const.mul hg'c'.neg).intervalIntegrable)
        intro t ht
        have hng : 0 ≤ -g' t := neg_nonneg.mpr (hgneg t ht)
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (hgneg t ht)]
        exact (mul_le_mul_of_nonneg_left (hfnorm t ht) (by positivity)).trans_eq (mul_one _)
      _ = _ := by rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, hFTC]; ring
  have henda : ‖C*(g a : ℂ)*f a‖ ≤ ‖C‖*g a := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hga]
    exact (mul_le_mul_of_nonneg_left (hfnorm a ⟨le_rfl,hab⟩) (by positivity)).trans_eq (mul_one _)
  have hendb : ‖C*(g b : ℂ)*f b‖ ≤ ‖C‖*g b := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgb]
    exact (mul_le_mul_of_nonneg_left (hfnorm b ⟨hab,le_rfl⟩) (by positivity)).trans_eq (mul_one _)
  rw [hibp]
  calc
    _ ≤ ‖C*(g b : ℂ)*f b - C*(g a : ℂ)*f a‖ +
        ‖∫ t in a..b, C*(g' t : ℂ)*f t‖ := norm_sub_le _ _
    _ ≤ (‖C‖*g b+‖C‖*g a)+‖C‖*(g a-g b) :=
      add_le_add ((norm_sub_le _ _).trans (add_le_add hendb henda)) hint
    _ = _ := by ring

/-- An explicit tail estimate, uniform in the upper endpoint. -/
theorem norm_monomial_integral_tail_le (k : ℕ) (hk : 1 ≤ k)
    {A P β : ℝ} (hA : 0 < A) (hAP : A ≤ P) (hβ : β ≠ 0) :
    ‖∫ t in A..P, e (β*t^k)‖ ≤ 1/(Real.pi*|β| *(k : ℝ)*A^(k-1)) := by
  let m : ℤ := -((k-1 : ℕ) : ℤ)
  let g : ℝ → ℝ := fun t => t^m
  let g' : ℝ → ℝ := fun t => (m : ℝ)*t^(m-1)
  let C : ℂ := (((2*Real.pi*β*(k : ℝ) : ℝ) : ℂ)*Complex.I)⁻¹
  have hkt : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hpos : ∀ t ∈ Set.Icc A P, 0 < t := fun t ht => hA.trans_le ht.1
  have hgc : ContinuousOn g (Set.Icc A P) :=
    continuousOn_id.zpow₀ m (fun t ht => Or.inl (ne_of_gt (hpos t ht)))
  have hg'c : ContinuousOn g' (Set.Icc A P) :=
    continuousOn_const.mul
      (continuousOn_id.zpow₀ (m-1) (fun t ht => Or.inl (ne_of_gt (hpos t ht))))
  have hgd : ∀ t ∈ Set.Icc A P, HasDerivAt g (g' t) t :=
    fun t ht => hasDerivAt_zpow m t (Or.inl (ne_of_gt (hpos t ht)))
  have hgneg : ∀ t ∈ Set.Icc A P, g' t ≤ 0 := by
    intro t ht
    have hm : (m : ℝ) ≤ 0 := by
      dsimp [m]
      push_cast
      exact neg_nonpos.mpr (Nat.cast_nonneg _)
    exact mul_nonpos_of_nonpos_of_nonneg hm (zpow_nonneg (hpos t ht).le _)
  have hfc : Continuous (fun t : ℝ => e (β*t^k)) := by unfold e; fun_prop
  have hident : ∀ t ∈ Set.Icc A P,
      C*(g t : ℂ)*deriv (fun x : ℝ => e (β*x^k)) t = e (β*t^k) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (hpos t ht)
    have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0
    have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hπc : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [deriv_monomial_e]
    dsimp [C, g, m]
    simp only [zpow_neg, zpow_natCast, Complex.ofReal_inv, Complex.ofReal_pow]
    push_cast
    field_simp [hβc, htc, hkc, hπc, Complex.I_ne_zero]
  have hmain := norm_integral_le_two_mul_of_reciprocal_deriv hAP C
    hfc.continuousOn (continuous_deriv_monomial_e k β).continuousOn hgc hg'c
    (fun t _ => (hasDerivAt_monomial_e k β t).differentiableAt.hasDerivAt)
    hgd hident (fun t _ => (norm_e _).le)
    (zpow_nonneg hA.le m) (zpow_nonneg (hA.le.trans hAP) m) hgneg
  have hCnorm : ‖C‖ = (2*Real.pi*|β| *(k : ℝ))⁻¹ := by
    dsimp [C]
    simp only [norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg Real.pi_pos.le, abs_of_nonneg (a := (k : ℝ)) (Nat.cast_nonneg k)]
  calc
    _ ≤ 2*‖C‖*g A := hmain
    _ = _ := by
      rw [hCnorm]
      dsimp [g,m]
      rw [zpow_neg, zpow_natCast]
      field_simp [hkt, hβ, abs_ne_zero.mpr hβ, Real.pi_ne_zero, ne_of_gt hA]

/-- Split the full integral before its stationary endpoint at zero, then
apply the explicit tail estimate. -/
theorem norm_monomialIntegral_split_le (k : ℕ) (hk : 1 ≤ k)
    {A P β : ℝ} (hA : 0 < A) (hAP : A ≤ P) (hβ : β ≠ 0) :
    ‖monomialIntegral k P β‖ ≤ A+1/(Real.pi*|β| *(k : ℝ)*A^(k-1)) := by
  have hfc : Continuous (fun t : ℝ => e (β*t^k)) := by unfold e; fun_prop
  unfold monomialIntegral
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hfc.intervalIntegrable 0 A) (hfc.intervalIntegrable A P)]
  exact (norm_add_le _ _).trans (add_le_add (norm_monomialIntegral_le k hA.le β)
    (norm_monomial_integral_tail_le k hk hA hAP hβ))

/-- Optimizing the split at the scale where `|β| A^k = 1`. -/
theorem norm_monomialIntegral_le_at_scale (k : ℕ) (hk : 1 ≤ k)
    {A P β : ℝ} (hA : 0 < A) (hP : 0 ≤ P) (hscale : |β| *A^k = 1) :
    ‖monomialIntegral k P β‖ ≤ (1+1/(Real.pi*(k : ℝ)))*A := by
  have hcoef : 0 ≤ 1/(Real.pi*(k : ℝ)) := by positivity
  by_cases hAP : A ≤ P
  · have hβ : β ≠ 0 := by intro h; simp [h] at hscale
    have hkt : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hpow : A^(k-1)*A = A^k := by rw [← pow_succ, Nat.sub_add_cancel hk]
    have htail : 1/(Real.pi*|β| *(k : ℝ)*A^(k-1)) = A/(Real.pi*(k : ℝ)) := by
      field_simp [Real.pi_ne_zero, hkt, abs_ne_zero.mpr hβ, ne_of_gt hA]
      rw [mul_assoc, hpow, hscale]
    calc
      _ ≤ A+1/(Real.pi*|β| *(k : ℝ)*A^(k-1)) :=
        norm_monomialIntegral_split_le k hk hA hAP hβ
      _ = _ := by rw [htail]; ring
  · exact (norm_monomialIntegral_le k hP β).trans
      ((le_of_not_ge hAP).trans (by nlinarith))

/-- The standard power decay bound for the actual monomial integral.
The zero-frequency case is handled separately by the length bound. -/
theorem norm_monomialIntegral_decay (k : ℕ) (hk : 1 ≤ k)
    {P β : ℝ} (hP : 0 ≤ P) (hβ : β ≠ 0) :
    ‖monomialIntegral k P β‖ ≤ 2*|β| ^ (-(k : ℝ)⁻¹) := by
  have hkt : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hβpos : 0 < |β| := abs_pos.mpr hβ
  have hscale : |β| *(|β| ^ (-(k : ℝ)⁻¹))^k = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hβpos.le, neg_mul,
      inv_mul_cancel₀ hkt, Real.rpow_neg_one, mul_inv_cancel₀ hβpos.ne']
  have hbound := norm_monomialIntegral_le_at_scale k hk
    (Real.rpow_pos_of_pos hβpos _) hP hscale
  have hπk : 1 ≤ Real.pi*(k : ℝ) := by nlinarith [Real.two_le_pi]
  have hcoef : 1+1/(Real.pi*(k : ℝ)) ≤ 2 := by
    have := (div_le_one (lt_of_lt_of_le zero_lt_one hπk)).mpr hπk
    linarith
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hβpos.le _))

theorem norm_monomialIntegral_le_min (k : ℕ) (hk : 1 ≤ k)
    {P β : ℝ} (hP : 0 ≤ P) (hβ : β ≠ 0) :
    ‖monomialIntegral k P β‖ ≤ min P (2*|β| ^ (-(k : ℝ)⁻¹)) :=
  le_min (norm_monomialIntegral_le k hP β) (norm_monomialIntegral_decay k hk hP hβ)

theorem continuous_monomialIntegral (k : ℕ) (P : ℝ) :
    Continuous (monomialIntegral k P) := by
  unfold monomialIntegral
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry e
  fun_prop

theorem monomialIntegral_neg (k : ℕ) {P : ℝ} (hP : 0 ≤ P) (β : ℝ) :
    monomialIntegral k P (-β) = starRingEnd ℂ (monomialIntegral k P β) := by
  unfold monomialIntegral
  rw [intervalIntegral.integral_of_le hP, intervalIntegral.integral_of_le hP,
    ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  simp only [conj_e, neg_mul]

theorem norm_monomialIntegral_neg (k : ℕ) {P : ℝ} (hP : 0 ≤ P) (β : ℝ) :
    ‖monomialIntegral k P (-β)‖ = ‖monomialIntegral k P β‖ := by
  rw [monomialIntegral_neg k hP, Complex.norm_conj]

theorem monomial_integral_moment_tail_pointwise (k s : ℕ) (hk : 1 ≤ k)
    {P β : ℝ} (hP : 0 ≤ P) (hβ : 0 < β) :
    ‖monomialIntegral k P β‖^s ≤ (2 : ℝ)^s*β^(-(s : ℝ)/(k : ℝ)) := by
  calc
    _ ≤ (2*β^(-(k : ℝ)⁻¹))^s := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [abs_of_pos hβ] using norm_monomialIntegral_decay k hk hP hβ.ne'
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast (β^(-(k : ℝ)⁻¹)) s, ← Real.rpow_mul hβ.le]
      congr 2
      ring

theorem integrableOn_monomial_moment_tail (k s : ℕ) (hk : 1 ≤ k)
    (hks : k < s) {P : ℝ} (hP : 0 ≤ P) :
    IntegrableOn (fun β => ‖monomialIntegral k P β‖^s) (Set.Ioi 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsr : (k : ℝ) < s := by exact_mod_cast hks
  have hexp : -(s : ℝ)/(k : ℝ) < -1 := (div_lt_iff₀ hkpos).mpr (by linarith)
  have hint := (integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul ((2 : ℝ)^s)
  apply hint.mono' (((continuous_monomialIntegral k P).norm.pow s).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with β hβ
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) s)]
  exact monomial_integral_moment_tail_pointwise k s hk hP (zero_lt_one.trans hβ)

theorem monomial_moment_tail_integral_le (k s : ℕ) (hk : 1 ≤ k)
    (hks : k < s) {P : ℝ} (hP : 0 ≤ P) :
    (∫ β in Set.Ioi 1, ‖monomialIntegral k P β‖^s) ≤
      (2 : ℝ)^s*(k : ℝ)/((s : ℝ)-k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsr : (k : ℝ) < s := by exact_mod_cast hks
  have hexp : -(s : ℝ)/(k : ℝ) < -1 := (div_lt_iff₀ hkpos).mpr (by linarith)
  have htail := integrableOn_Ioi_rpow_of_lt hexp zero_lt_one
  calc
    _ ≤ ∫ β in Set.Ioi 1, (2 : ℝ)^s*β^(-(s : ℝ)/(k : ℝ)) := by
      apply setIntegral_mono_on (integrableOn_monomial_moment_tail k s hk hks hP)
        (htail.const_mul ((2 : ℝ)^s)) measurableSet_Ioi
      intro β hβ
      exact monomial_integral_moment_tail_pointwise k s hk hP (zero_lt_one.trans hβ)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp zero_lt_one, Real.one_rpow]
      field_simp [hkpos.ne', sub_ne_zero.mpr hsr.ne',
        show -(s : ℝ)+(k : ℝ) ≠ 0 by linarith]
      ring

theorem integrableOn_monomial_moment_positive (k s : ℕ) (hk : 1 ≤ k)
    (hks : k < s) {P : ℝ} (hP : 0 ≤ P) :
    IntegrableOn (fun β => ‖monomialIntegral k P β‖^s) (Set.Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact (((continuous_monomialIntegral k P).norm.pow s).integrableOn_Icc.mono_set
    Set.Ioc_subset_Icc_self).union (integrableOn_monomial_moment_tail k s hk hks hP)

theorem integrable_monomial_moment (k s : ℕ) (hk : 1 ≤ k)
    (hks : k < s) {P : ℝ} (hP : 0 ≤ P) :
    Integrable (fun β => ‖monomialIntegral k P β‖^s) := by
  have hpos := integrableOn_monomial_moment_positive k s hk hks hP
  have hneg : IntegrableOn (fun β => ‖monomialIntegral k P β‖^s) (Set.Iic 0) := by
    apply (integrableOn_Iic_iff_integrableOn_Iio (f := fun β => ‖monomialIntegral k P β‖^s)).mpr
    have h := (show IntegrableOn (fun β => ‖monomialIntegral k P β‖^s)
      (Set.Ioi (-(0 : ℝ))) by simpa using hpos).comp_neg_Iio
    simpa only [norm_monomialIntegral_neg k hP] using h
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hneg.union hpos

theorem unit_monomial_moment_le (k s : ℕ) (hk : 1 ≤ k) (hks : k < s) :
    (∫ β : ℝ, ‖monomialIntegral k 1 β‖^s) ≤
      2*(1+(2 : ℝ)^s*(k : ℝ)/((s : ℝ)-k)) := by
  have hpos := integrableOn_monomial_moment_positive k s hk hks (P := 1) zero_le_one
  have htail := integrableOn_monomial_moment_tail k s hk hks (P := 1) zero_le_one
  have hlow : (∫ β in Set.Ioc 0 1, ‖monomialIntegral k 1 β‖^s) ≤ 1 := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    calc
      _ ≤ ∫ _β in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_mono_on zero_le_one
          (((continuous_monomialIntegral k 1).norm.pow s).intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1)
        intro β _
        simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
          (norm_monomialIntegral_le k zero_le_one β) s
      _ = 1 := by simp
  have hhalf : (∫ β in Set.Ioi 0, ‖monomialIntegral k 1 β‖^s) ≤
      1+(2 : ℝ)^s*(k : ℝ)/((s : ℝ)-k) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hpos.mono_set Set.Ioc_subset_Ioi_self) htail]
    exact add_le_add hlow (monomial_moment_tail_integral_le k s hk hks zero_le_one)
  have habs : ∀ β : ℝ, ‖monomialIntegral k 1 |β|‖^s = ‖monomialIntegral k 1 β‖^s := by
    intro β
    rcases le_or_gt 0 β with hβ | hβ
    · rw [abs_of_nonneg hβ]
    · rw [abs_of_neg hβ, norm_monomialIntegral_neg k zero_le_one]
  calc
    _ = ∫ β : ℝ, ‖monomialIntegral k 1 |β|‖^s :=
      integral_congr_ae (Filter.Eventually.of_forall (fun β => (habs β).symm))
    _ = 2*(∫ β in Set.Ioi 0, ‖monomialIntegral k 1 β‖^s) :=
      integral_comp_abs (f := fun β => ‖monomialIntegral k 1 β‖^s)
    _ ≤ _ := mul_le_mul_of_nonneg_left hhalf (by norm_num)

theorem monomial_moment_scale (k s : ℕ) (hks : k ≤ s) {P : ℝ} (hP : 0 < P) :
    (∫ β : ℝ, ‖monomialIntegral k P β‖^s) =
      P^(s-k)*(∫ β : ℝ, ‖monomialIntegral k 1 β‖^s) := by
  simp_rw [monomialIntegral_scale k P, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hP, mul_pow]
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_mul_right
    (fun β => ‖monomialIntegral k 1 β‖^s) (P^k)]
  simp only [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hP.le _)), smul_eq_mul]
  rw [show P^s = P^(s-k)*P^k by rw [← pow_add, Nat.sub_add_cancel hks]]
  field_simp

/-- The complete ordinary singular-integral moment estimate needed in
major-arc estimates. The constant is explicit and valid for every `s > k`. -/
theorem full_monomial_moment_le (k s : ℕ) (hk : 1 ≤ k) (hks : k < s)
    {P : ℝ} (hP : 0 < P) :
    (∫ β : ℝ, ‖monomialIntegral k P β‖^s) ≤
      (2*(1+(2 : ℝ)^s*(k : ℝ)/((s : ℝ)-k)))*P^(s-k) := by
  rw [monomial_moment_scale k s hks.le hP]
  exact (mul_le_mul_of_nonneg_left (unit_monomial_moment_le k s hk hks)
    (pow_nonneg hP.le _)).trans_eq (mul_comm _ _)

#print axioms norm_integral_le_two_mul_of_reciprocal_deriv
#print axioms norm_monomial_integral_tail_le
#print axioms norm_monomialIntegral_split_le
#print axioms norm_monomialIntegral_decay
#print axioms integrable_monomial_moment
#print axioms full_monomial_moment_le

end Waring.EndgameCompletion
