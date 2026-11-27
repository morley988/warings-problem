import Waring.HighOrderEndgame
import Waring.EvenMoments

/-!
# Degree-eight pruning through ordinary even moments

The pruning argument needs a strong full 90th smooth moment, not specifically
the stronger 42nd smooth moment used by the original interface. Counting
inclusion bounds every even smooth moment by the corresponding ordinary
moment. The resulting alternative endgame can therefore use a strong ordinary
90th moment. Every substantive source estimate remains an explicit hypothesis.
-/

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped BigOperators ENNReal Topology

namespace Waring.EndgameCompletion
open SmoothMoments MixedEndgame AdmissibleMinorArc Certificate Pruning

/-- The full ordinary moment uses precisely the same interval and cutoff as
the ordinary sum already appearing in the Waring representation integral. -/
def ordinaryMoment (k p : ℕ) (P : ℝ) : ℝ :=
  ∫ α in (0 : ℝ)..1, ‖ordinaryWeyl k P α‖ ^ p

theorem ordinaryMoment_integrable (k p : ℕ) (P : ℝ) :
    IntervalIntegrable (fun α => ‖ordinaryWeyl k P α‖ ^ p) volume 0 1 :=
  ((continuous_ordinary k P).norm.pow p).intervalIntegrable 0 1

theorem ordinaryMoment_nonneg (k p : ℕ) (P : ℝ) :
    0 ≤ ordinaryMoment k p P := by
  unfold ordinaryMoment
  exact intervalIntegral.integral_nonneg_of_forall zero_le_one
    (fun α => pow_nonneg (norm_nonneg _) _)

theorem ordinaryMoment_even_eq_frequency (k r : ℕ) (P : ℝ) :
    ordinaryMoment k (2*r) P =
      frequencyEvenMoment (ordinaryNumbers P) (fun n => ((n^k : ℕ) : ℤ)) r := by
  unfold ordinaryMoment ordinaryWeyl frequencyEvenMoment
  simp_rw [phase_eq_fourier]

/-- Integral monotonicity under inclusion follows from exact even-moment
counts; no pointwise comparison of the two exponential sums is used. -/
theorem smoothMoment_even_le_ordinaryMoment (k r : ℕ) (P R : ℝ) :
    smoothMoment k (2*r) P R ≤ ordinaryMoment k (2*r) P := by
  rw [smoothMoment_even_eq_frequency, ordinaryMoment_even_eq_frequency]
  apply frequencyEvenMoment_mono
  intro n hn
  exact Finset.mem_Icc.mpr (mem_smoothNumbers.mp hn).1

theorem strong_ordinary90_to_smooth90 {P R C : ℝ}
    (h : ordinaryMoment 8 90 P ≤ C*P^82) :
    smoothMoment 8 90 P R ≤ C*P^82 := by
  exact (smoothMoment_even_le_ordinaryMoment 8 45 P R).trans h

theorem norm_ordinaryWeyl_le (k : ℕ) {P : ℝ} (α : ℝ) (hP : 0 ≤ P) :
    ‖ordinaryWeyl k P α‖ ≤ P := by
  unfold ordinaryWeyl
  calc
    ‖∑ n ∈ ordinaryNumbers P, phase k n α‖ ≤
        ∑ n ∈ ordinaryNumbers P, ‖phase k n α‖ := norm_sum_le _ _
    _ = (⌊P⌋₊ : ℝ) := by simp [ordinaryNumbers]
    _ ≤ P := Nat.floor_le hP

theorem ordinaryArcMoment_full (k p : ℕ) (P : ℝ) :
    ordinaryArcMoment k p P (Set.Ioc 0 1) = ENNReal.ofReal (ordinaryMoment k p P) := by
  unfold ordinaryArcMoment absoluteOrdinary ordinaryMoment
  rw [intervalIntegral.integral_of_le zero_le_one,
    ofReal_integral_eq_lintegral_ofReal (ordinaryMoment_integrable k p P).1
      (Filter.Eventually.of_forall (fun α => pow_nonneg (norm_nonneg _) p))]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]

/-- Raising an ordinary moment on any measurable or nonmeasurable arc set
costs at most the corresponding power of the length cutoff. -/
theorem ordinaryArcMoment_order_growth (k p q : ℕ) {P : ℝ} (A : Set ℝ)
    (hpq : p ≤ q) (hP : 0 ≤ P) :
    ordinaryArcMoment k q P A ≤
      ENNReal.ofReal (P^(q-p))*ordinaryArcMoment k p P A := by
  have hpoint (α : ℝ) :
      absoluteOrdinary k P α^q ≤
        ENNReal.ofReal (P^(q-p))*absoluteOrdinary k P α^p := by
    have hnorm : absoluteOrdinary k P α ≤ ENNReal.ofReal P :=
      ENNReal.ofReal_le_ofReal (norm_ordinaryWeyl_le k α hP)
    calc
      _ = absoluteOrdinary k P α^(q-p)*absoluteOrdinary k P α^p := by
        rw [← pow_add, Nat.sub_add_cancel hpq]
      _ ≤ ENNReal.ofReal P^(q-p)*absoluteOrdinary k P α^p :=
        mul_le_mul_right' (pow_le_pow_left' hnorm _) _
      _ = _ := by rw [ENNReal.ofReal_pow hP]
  unfold ordinaryArcMoment
  calc
    _ ≤ ∫⁻ α, ENNReal.ofReal (P^(q-p))*absoluteOrdinary k P α^p ∂volume.restrict A :=
      lintegral_mono hpoint
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The strong ordinary 90th moment follows from the ordinary major 12th
moment and the minor 72nd moment already required in the degree-eight
argument. Epsilon may be any real number at most one. -/
theorem ordinary90_of_major12_minor72 {P Cmajor Cminor ε : ℝ}
    (hP : 1 ≤ P) (hCmajor : 0 ≤ Cmajor) (hCminor : 0 ≤ Cminor) (hε : ε ≤ 1)
    {major minor : Set ℝ} (hcover : major ∪ minor = Set.Ioc 0 1)
    (hmajor : ordinaryArcMoment 8 12 P major ≤ ENNReal.ofReal (Cmajor*P^4))
    (hminor : ordinaryArcMoment 8 72 P minor ≤ ENNReal.ofReal (Cminor*P^(63+ε : ℝ))) :
    ordinaryMoment 8 90 P ≤ (Cmajor+Cminor)*P^82 := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hmajor90 : ordinaryArcMoment 8 90 P major ≤ ENNReal.ofReal (Cmajor*P^82) := by
    calc
      _ ≤ ENNReal.ofReal (P^78)*ordinaryArcMoment 8 12 P major :=
        ordinaryArcMoment_order_growth 8 12 90 major (by norm_num) hPpos.le
      _ ≤ ENNReal.ofReal (P^78)*ENNReal.ofReal (Cmajor*P^4) :=
        mul_le_mul_left' hmajor _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hexponent : P^18*P^(63+ε : ℝ) ≤ P^82 := by
    calc
      _ = P^(81+ε : ℝ) := by
        rw [← Real.rpow_natCast P 18, ← Real.rpow_add hPpos]
        congr 1
        ring
      _ ≤ P^(82 : ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
      _ = _ := Real.rpow_natCast P 82
  have hminor90 : ordinaryArcMoment 8 90 P minor ≤ ENNReal.ofReal (Cminor*P^82) := by
    calc
      _ ≤ ENNReal.ofReal (P^18)*ordinaryArcMoment 8 72 P minor :=
        ordinaryArcMoment_order_growth 8 72 90 minor (by norm_num) hPpos.le
      _ ≤ ENNReal.ofReal (P^18)*ENNReal.ofReal (Cminor*P^(63+ε : ℝ)) :=
        mul_le_mul_left' hminor _
      _ = ENNReal.ofReal (Cminor*(P^18*P^(63+ε : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (Cminor*P^82) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexponent hCminor)
  have hbound : ENNReal.ofReal (ordinaryMoment 8 90 P) ≤
      ENNReal.ofReal ((Cmajor+Cminor)*P^82) := by
    rw [← ordinaryArcMoment_full, ← hcover]
    calc
      _ ≤ ordinaryArcMoment 8 90 P major + ordinaryArcMoment 8 90 P minor :=
        lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal (Cmajor*P^82)+ENNReal.ofReal (Cminor*P^82) :=
        add_le_add hmajor90 hminor90
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

theorem smooth90_of_ordinary_major12_minor72 {P R Cmajor Cminor ε : ℝ}
    (hP : 1 ≤ P) (hCmajor : 0 ≤ Cmajor) (hCminor : 0 ≤ Cminor) (hε : ε ≤ 1)
    {major minor : Set ℝ} (hcover : major ∪ minor = Set.Ioc 0 1)
    (hmajor : ordinaryArcMoment 8 12 P major ≤ ENNReal.ofReal (Cmajor*P^4))
    (hminor : ordinaryArcMoment 8 72 P minor ≤ ENNReal.ofReal (Cminor*P^(63+ε : ℝ))) :
    smoothMoment 8 90 P R ≤ (Cmajor+Cminor)*P^82 :=
  strong_ordinary90_to_smooth90
    (ordinary90_of_major12_minor72 hP hCmajor hCminor hε hcover hmajor hminor)

/-- The actual Holder pruning estimate depends directly on the 90th smooth
moment. This avoids importing a separate strong smooth 42nd-moment theorem. -/
theorem pruning8_abs_bound_of_strong90 {P R W Cf Cg : ℝ}
    (hP : 0 < P) (hW : 0 < W) (hCf : 0 < Cf) (hCg : 0 < Cg)
    (n : ℕ) {A : Set ℝ} (hA : A ⊆ Set.Ioc 0 1)
    (hF : ordinaryArcMoment 8 12 P A ≤
      ENNReal.ofReal (Cf*P^4*W^(-(1/16 : ℝ))))
    (hg : smoothMoment 8 90 P R ≤ Cg*P^82) :
    |arcContribution 8 8 30 P R n A| ≤
      (Cf^(2/3 : ℝ)*Cg^(1/3 : ℝ))*P^(30 : ℝ)*W^(-(1/24 : ℝ)) := by
  have hg90 : smoothArcMoment 8 90 P R A ≤ ENNReal.ofReal (Cg*P^82) :=
    (smoothArcMoment_le_full 8 90 P R hA).trans (ENNReal.ofReal_le_ofReal hg)
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

theorem pruning8_isLittleO_of_strong90 (P R W : ℕ → ℝ) (A : ℕ → Set ℝ)
    (hP : Tendsto P atTop atTop) (hW : Tendsto W atTop atTop)
    {Cf Cg : ℝ} (hCf : 0 < Cf) (hCg : 0 < Cg)
    (hA : ∀ᶠ n in atTop, A n ⊆ Set.Ioc 0 1)
    (hF : ∀ᶠ n in atTop, ordinaryArcMoment 8 12 (P n) (A n) ≤
      ENNReal.ofReal (Cf*(P n)^4*(W n)^(-(1/16 : ℝ))))
    (hg : ∀ᶠ n in atTop, smoothMoment 8 90 (P n) (R n) ≤ Cg*(P n)^82) :
    (fun n => arcContribution 8 8 30 (P n) (R n) n (A n)) =o[atTop]
      (fun n => (P n)^(30 : ℝ)) := by
  apply width_saving_isLittleO (δ := (1/24 : ℝ)) (by norm_num) hW
  apply IsBigO.of_bound (Cf^(2/3 : ℝ)*Cg^(1/3 : ℝ))
  filter_upwards [hP.eventually_gt_atTop 0,hW.eventually_gt_atTop 0,hA,hF,hg]
    with n hPn hWn hAn hFn hgn
  have hb := pruning8_abs_bound_of_strong90 hPn hWn hCf hCg n hAn hFn hgn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (P n)^(30 : ℝ)*(W n)^(-(1/24 : ℝ))), mul_assoc] using hb

/-- Ordinary even-moment domination supplies the smooth pruning input with
no smoothness restriction and no epsilon loss. -/
theorem pruning8_isLittleO_of_ordinary90 (P R W : ℕ → ℝ) (A : ℕ → Set ℝ)
    (hP : Tendsto P atTop atTop) (hW : Tendsto W atTop atTop)
    {Cf Co : ℝ} (hCf : 0 < Cf) (hCo : 0 < Co)
    (hA : ∀ᶠ n in atTop, A n ⊆ Set.Ioc 0 1)
    (hF : ∀ᶠ n in atTop, ordinaryArcMoment 8 12 (P n) (A n) ≤
      ENNReal.ofReal (Cf*(P n)^4*(W n)^(-(1/16 : ℝ))))
    (ho : ∀ᶠ n in atTop, ordinaryMoment 8 90 (P n) ≤ Co*(P n)^82) :
    (fun n => arcContribution 8 8 30 (P n) (R n) n (A n)) =o[atTop]
      (fun n => (P n)^(30 : ℝ)) := by
  apply pruning8_isLittleO_of_strong90 P R W A hP hW hCf hCo hA hF
  exact ho.mono (fun n hn => strong_ordinary90_to_smooth90 hn)

/-- An alternative end-to-end degree-eight implication. The previously
separate strong smooth 42nd-moment premise has been replaced by an ordinary
90th-moment premise. Seed, policy and arc estimates remain explicit. -/
theorem waring8_from_high_order_sources_and_ordinary90
    (hseed : HighOrderAdmissibleCurve 8 source8)
    (hcoefficientSeed : HighOrderAdmissibleCurve 16 coefficientSource8)
    (hsound : ∀ i, i < policies8.size → AnalyticPolicySound 8 policies8[i]!) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R W : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop → Tendsto W atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n^η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*(P n)^(30 : ℝ) ≤
          arcContribution 8 8 30 (P n) (R n) n (core n)) →
        ∀ Cf Co : ℝ, 0 < Cf → 0 < Co →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 12 (P n) (pruning n) ≤
          ENNReal.ofReal (Cf*(P n)^4*(W n)^(-(1/16 : ℝ)))) →
        (∀ᶠ n in atTop, ordinaryMoment 8 90 (P n) ≤ Co*(P n)^82) →
        ∀ C₀ : ℝ≥0∞, C₀ ≠ ⊤ →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 72 (P n) (minor n) ≤
          C₀*ENNReal.ofReal (P n)^(63+epsilon8)) →
        WaringBound 8 38 := by
  obtain ⟨η,hη,hend⟩ := waring8_from_seed_tables_conditional
    (source8_admissible_of_high hseed)
    (coefficientSource8_admissible_of_high hcoefficientSeed) hsound
  refine ⟨η,hη,?_⟩
  intro P R W core pruning minor hP hW hR hpartition c hc hcore Cf Co hCf hCo hF ho C₀ hC₀ hm
  have hA := hpartition.mono (fun _ hn => EndgameFromPublishedInputs.pruning_subset_period hn)
  exact hend P R core pruning minor hP hR hpartition c hc hcore
    (pruning8_isLittleO_of_ordinary90 P R W pruning hP hW hCf hCo hA hF ho) C₀ hC₀ hm

/-- The degree-eight conclusion using only ordinary moments for pruning.
The high ordinary moment is derived from the existing minor input and a
full ordinary-major 12th-moment estimate; no strong smooth moment is assumed. -/
theorem waring8_from_high_order_sources_and_ordinary_major12
    (hseed : HighOrderAdmissibleCurve 8 source8)
    (hcoefficientSeed : HighOrderAdmissibleCurve 16 coefficientSource8)
    (hsound : ∀ i, i < policies8.size → AnalyticPolicySound 8 policies8[i]!) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (P R W : ℕ → ℝ) (core pruning minor : ℕ → Set ℝ),
        Tendsto P atTop atTop → Tendsto W atTop atTop →
        (∀ᶠ n in atTop, 1 ≤ R n ∧ R n ≤ P n^η) →
        (∀ᶠ n in atTop, ArcPartition (core n) (pruning n) (minor n)) →
        ∀ c : ℝ, 0 < c →
        (∀ᶠ n in atTop, c*(P n)^(30 : ℝ) ≤
          arcContribution 8 8 30 (P n) (R n) n (core n)) →
        ∀ Cf Cmajor Cminor : ℝ, 0 < Cf → 0 < Cmajor → 0 < Cminor →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 12 (P n) (pruning n) ≤
          ENNReal.ofReal (Cf*(P n)^4*(W n)^(-(1/16 : ℝ)))) →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 12 (P n) (core n ∪ pruning n) ≤
          ENNReal.ofReal (Cmajor*(P n)^4)) →
        (∀ᶠ n in atTop, ordinaryArcMoment 8 72 (P n) (minor n) ≤
          ENNReal.ofReal (Cminor*(P n)^(63+epsilon8))) →
        WaringBound 8 38 := by
  obtain ⟨η,hη,hend⟩ :=
    waring8_from_high_order_sources_and_ordinary90 hseed hcoefficientSeed hsound
  refine ⟨η,hη,?_⟩
  intro P R W core pruning minor hP hW hR hpartition c hc hcore
    Cf Cmajor Cminor hCf hCmajor hCminor hF hmajor hminor
  have ho : ∀ᶠ n in atTop,
      ordinaryMoment 8 90 (P n) ≤ (Cmajor+Cminor)*(P n)^82 := by
    filter_upwards [hP.eventually_ge_atTop 1,hpartition,hmajor,hminor]
      with n hPn hpart hmajor_n hminor_n
    apply ordinary90_of_major12_minor72 hPn hCmajor.le hCminor.le
      (by norm_num [epsilon8]) _ hmajor_n hminor_n
    simpa only [Set.union_assoc] using hpart.cover
  have hm : ∀ᶠ n in atTop, ordinaryArcMoment 8 72 (P n) (minor n) ≤
      ENNReal.ofReal Cminor*ENNReal.ofReal (P n)^(63+epsilon8) := by
    filter_upwards [hP.eventually_gt_atTop 0,hminor] with n hPn hn
    rw [ENNReal.ofReal_rpow_of_pos hPn, ← ENNReal.ofReal_mul hCminor.le]
    exact hn
  exact hend P R W core pruning minor hP hW hR hpartition c hc hcore
    Cf (Cmajor+Cminor) hCf (add_pos hCmajor hCminor) hF ho
    (ENNReal.ofReal Cminor) ENNReal.ofReal_ne_top hm

#print axioms smoothMoment_even_le_ordinaryMoment
#print axioms ordinary90_of_major12_minor72
#print axioms smooth90_of_ordinary_major12_minor72
#print axioms pruning8_isLittleO_of_ordinary90
#print axioms waring8_from_high_order_sources_and_ordinary90
#print axioms waring8_from_high_order_sources_and_ordinary_major12

end Waring.EndgameCompletion
