import Waring.EndgameCompletionOrdinary
import Waring.QuadraticModulation
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Data.Nat.Periodic

/-!
# Ordinary sums close to rational points

This file develops actual major-arc source estimates, starting from the
bounded discrepancy of a periodic sequence and Abel summation.  Its sums use
the same positive integers and additive exponential as `ordinaryWeyl`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Waring.EndgameCompletion
open SmoothMoments QuadraticModulation

/-- One period's average for a complex sequence on the natural numbers. -/
def periodicMean (c : ℕ → ℂ) (q : ℕ) : ℂ :=
  (∑ n ∈ Finset.range q, c n) / q

theorem norm_periodicMean_le {c : ℕ → ℂ} {q : ℕ} (hq : 0 < q)
    (hc : ∀ n, ‖c n‖ ≤ 1) : ‖periodicMean c q‖ ≤ 1 := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  unfold periodicMean
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_one hqr).mpr
  calc
    ‖∑ n ∈ Finset.range q, c n‖ ≤ ∑ n ∈ Finset.range q, ‖c n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range q, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hc n)
    _ = q := by simp

theorem periodic_sum_full_blocks {c : ℕ → ℂ} {q : ℕ}
    (hper : Function.Periodic c q) (m : ℕ) :
    (∑ n ∈ Finset.range (m*q), c n) = (m : ℂ) * ∑ n ∈ Finset.range q, c n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hshift : (∑ n ∈ Finset.range q, c (m*q+n)) = ∑ n ∈ Finset.range q, c n := by
        apply Finset.sum_congr rfl
        intro n _
        simpa only [Nat.add_comm] using hper.nat_mul m n
      rw [hshift, Nat.cast_succ]
      ring

/-- After subtracting the period average, every initial sum is bounded by
twice the period, independently of its length. -/
theorem norm_periodic_sum_sub_mean_le {c : ℕ → ℂ} {q : ℕ}
    (hq : 0 < q) (hper : Function.Periodic c q)
    (hc : ∀ n, ‖c n‖ ≤ 1) (N : ℕ) :
    ‖(∑ n ∈ Finset.range N, c n) - (N : ℂ)*periodicMean c q‖ ≤ 2*q := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have hdecomp : (∑ n ∈ Finset.range N, c n) =
      (N/q : ℕ) * (∑ n ∈ Finset.range q, c n) + ∑ n ∈ Finset.range (N%q), c n := by
    nth_rw 1 [← Nat.div_add_mod N q]
    rw [Nat.mul_comm q (N/q), Finset.sum_range_add, periodic_sum_full_blocks hper]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    simpa only [Nat.add_comm] using hper.nat_mul (N/q) n
  have hcancel : (∑ n ∈ Finset.range N, c n) - (N : ℂ)*periodicMean c q =
      (∑ n ∈ Finset.range (N%q), c n) - (N%q : ℕ)*periodicMean c q := by
    rw [hdecomp]
    have hN : (N : ℂ) = (N/q : ℕ)*(q : ℂ) + (N%q : ℕ) := by
      exact_mod_cast (by simpa only [Nat.mul_comm] using (Nat.div_add_mod N q).symm :
        N = N/q*q + N%q)
    rw [hN]
    unfold periodicMean
    field_simp
    ring
  rw [hcancel]
  have hrem : ((N%q : ℕ) : ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt N hq).le
  calc
    _ ≤ ‖∑ n ∈ Finset.range (N%q), c n‖ + ‖(N%q : ℕ)*periodicMean c q‖ := norm_sub_le _ _
    _ ≤ (N%q : ℕ) + (N%q : ℕ) * 1 := by
      apply add_le_add
      · exact (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.range (N%q)) (fun n _ => hc n))
      · rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (norm_periodicMean_le hq hc) (Nat.cast_nonneg _)
    _ ≤ 2*q := by nlinarith

/-- Initial sums over positive integers, with a real endpoint. -/
def positivePartialSum (c : ℕ → ℂ) (P : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊P⌋₊, c n

theorem positivePartialSum_eq_range (c : ℕ → ℂ) (P : ℝ) :
    positivePartialSum c P = ∑ n ∈ Finset.range ⌊P⌋₊, c (n+1) := by
  simpa only [Finset.range_eq_Ico, Nat.zero_add,
    Finset.Ico_add_one_right_eq_Icc, positivePartialSum] using
      (Finset.sum_Ico_add' c 0 ⌊P⌋₊ 1).symm

/-- The period average also approximates a real-endpoint partial sum.
The extra unit from the floor is absorbed into a uniform `3q` bound. -/
theorem norm_positivePartialSum_sub_mean_le {c : ℕ → ℂ} {q : ℕ}
    (hq : 0 < q) (hper : Function.Periodic c q)
    (hc : ∀ n, ‖c n‖ ≤ 1) {P : ℝ} (hP : 0 ≤ P) :
    ‖positivePartialSum c P - (P : ℂ)*periodicMean (fun n => c (n+1)) q‖ ≤ 3*q := by
  let μ := periodicMean (fun n => c (n+1)) q
  have hμ : ‖μ‖ ≤ 1 := norm_periodicMean_le hq (fun n => hc (n+1))
  have hfloor : |(⌊P⌋₊ : ℝ) - P| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Nat.floor_le hP))]
    have := Nat.lt_floor_add_one P
    linarith
  have hmain : ‖positivePartialSum c P - (⌊P⌋₊ : ℂ)*μ‖ ≤ 2*q := by
    rw [positivePartialSum_eq_range]
    exact norm_periodic_sum_sub_mean_le hq (hper.add_const 1) (fun n => hc (n+1)) _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  calc
    _ = ‖(positivePartialSum c P - (⌊P⌋₊ : ℂ)*μ) +
        (((⌊P⌋₊ : ℝ)-P : ℝ) : ℂ)*μ‖ := by congr 1; simp only [Complex.ofReal_sub, Complex.ofReal_natCast]; ring
    _ ≤ ‖positivePartialSum c P - (⌊P⌋₊ : ℂ)*μ‖ +
        ‖(((⌊P⌋₊ : ℝ)-P : ℝ) : ℂ)*μ‖ := norm_add_le _ _
    _ ≤ 2*q+1 := by
      apply add_le_add hmain
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul hfloor hμ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    _ ≤ 3*q := by linarith

private def positiveSequence (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else c n

private theorem sum_positiveSequence (c : ℕ → ℂ) (P : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊P⌋₊, positiveSequence c n) = positivePartialSum c P := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp only [positiveSequence, ite_true, zero_add]
  rw [← Finset.Icc_add_one_left_eq_Ioc]
  unfold positivePartialSum
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Nat.zero_add, Finset.mem_Icc] at hn
  simp only [if_neg (Nat.ne_of_gt hn.1)]

/-- Abel summation expressed with precisely the positive partial sums used
by the ordinary Weyl sum. -/
theorem positive_sum_eq_abel (c : ℕ → ℂ) {f : ℝ → ℂ} {P : ℝ}
    (hP : 0 ≤ P) (hf : ∀ t, DifferentiableAt ℝ f t)
    (hf' : Continuous (deriv f)) :
    (∑ n ∈ Finset.Icc 1 ⌊P⌋₊, f n*c n) =
      f P*positivePartialSum c P -
        ∫ t in (0 : ℝ)..P, deriv f t*positivePartialSum c t := by
  have h := sum_mul_eq_sub_integral_mul (positiveSequence c) hP
    (fun t _ => hf t)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hP).mp (hf'.intervalIntegrable 0 P))
  have hleft : (∑ n ∈ Finset.Icc 0 ⌊P⌋₊, f n*positiveSequence c n) =
      ∑ n ∈ Finset.Icc 1 ⌊P⌋₊, f n*c n := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
    simp only [positiveSequence, ite_true, mul_zero, zero_add]
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Nat.zero_add, Finset.mem_Icc] at hn
    simp only [if_neg (Nat.ne_of_gt hn.1)]
  simpa only [hleft, sum_positiveSequence, ← intervalIntegral.integral_of_le hP] using h

/-- The exact remainder after replacing a periodic sequence by its mean. -/
theorem positive_sum_sub_mean_integral_eq (c : ℕ → ℂ) (μ : ℂ)
    {f : ℝ → ℂ} {P : ℝ} (hP : 0 ≤ P)
    (hf : ∀ t, DifferentiableAt ℝ f t) (hf' : Continuous (deriv f)) :
    (∑ n ∈ Finset.Icc 1 ⌊P⌋₊, f n*c n) - μ*(∫ t in (0 : ℝ)..P, f t) =
      f P*(positivePartialSum c P - (P : ℂ)*μ) -
        ∫ t in (0 : ℝ)..P, deriv f t*(positivePartialSum c t - (t : ℂ)*μ) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := f) (u' := deriv f) (v := fun t : ℝ => (t : ℂ)*μ) (v' := fun _ => μ)
    hfc.continuousOn (Complex.continuous_ofReal.mul continuous_const).continuousOn
    (fun t _ => (hf t).hasDerivAt)
    (fun t _ => by simpa using (hasDerivAt_id t).ofReal_comp.mul_const μ)
    (hf'.intervalIntegrable 0 P) (continuous_const.intervalIntegrable 0 P)
  have hsumint : IntervalIntegrable
      (fun t => deriv f t*positivePartialSum c t) volume 0 P := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hP).mpr
    simpa only [positivePartialSum] using
      integrableOn_mul_sum_Icc c (m := 1) (a := 0) (b := P) le_rfl
        ((intervalIntegrable_iff_integrableOn_Icc_of_le hP).mp (hf'.intervalIntegrable 0 P))
  have hlinint : IntervalIntegrable
      (fun t : ℝ => deriv f t*((t : ℂ)*μ)) volume 0 P :=
    (hf'.mul (Complex.continuous_ofReal.mul continuous_const)).intervalIntegrable 0 P
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, sub_zero,
    intervalIntegral.integral_mul_const] at hibp
  rw [positive_sum_eq_abel c hP hf hf']
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hsumint hlinint]
  linear_combination -hibp

/-- A uniform major-arc quadrature estimate from periodicity alone.
All assumptions concern an actual periodic sequence and an actual `C¹`
weight; no exponential-sum estimate is assumed. -/
theorem norm_positive_sum_sub_mean_integral_le {c : ℕ → ℂ} {q : ℕ}
    (hq : 0 < q) (hper : Function.Periodic c q) (hc : ∀ n, ‖c n‖ ≤ 1)
    {f : ℝ → ℂ} {P B D : ℝ} (hP : 0 ≤ P)
    (hf : ∀ t, DifferentiableAt ℝ f t) (hf' : Continuous (deriv f))
    (hB : ‖f P‖ ≤ B) (hD : ∀ t ∈ Set.Icc 0 P, ‖deriv f t‖ ≤ D) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊P⌋₊, f n*c n) -
        periodicMean (fun n => c (n+1)) q*(∫ t in (0 : ℝ)..P, f t)‖ ≤
      3*q*(B+P*D) := by
  let μ := periodicMean (fun n => c (n+1)) q
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 ⟨le_rfl,hP⟩)
  rw [positive_sum_sub_mean_integral_eq c μ hP hf hf']
  have hmain : ‖f P*(positivePartialSum c P - (P : ℂ)*μ)‖ ≤ B*(3*q) := by
    rw [norm_mul]
    exact mul_le_mul hB (norm_positivePartialSum_sub_mean_le hq hper hc hP)
      (norm_nonneg _) ((norm_nonneg _).trans hB)
  have hint : ‖∫ t in (0 : ℝ)..P,
      deriv f t*(positivePartialSum c t - (t : ℂ)*μ)‖ ≤ (D*(3*q))*P := by
    simpa only [sub_zero, abs_of_nonneg hP] using
      intervalIntegral.norm_integral_le_of_norm_le_const (C := D*(3*q))
        (f := fun t => deriv f t*(positivePartialSum c t - (t : ℂ)*μ))
        (a := 0) (b := P) (by
          intro t ht
          rw [Set.uIoc_of_le hP] at ht
          rw [norm_mul]
          exact mul_le_mul (hD t ⟨ht.1.le, ht.2⟩)
            (norm_positivePartialSum_sub_mean_le hq hper hc ht.1.le)
            (norm_nonneg _) hD0)
  exact (norm_sub_le _ _).trans ((add_le_add hmain hint).trans_eq (by ring))

theorem e_int (a : ℤ) : e (a : ℝ) = 1 := by
  unfold e
  rw [show (((2*Real.pi*(a : ℝ) : ℝ) : ℂ)*Complex.I) =
    (a : ℂ)*(2*Real.pi*Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I a

theorem e_add_int (x : ℝ) (a : ℤ) : e (x+a) = e x := by
  rw [e_add, e_int, mul_one]

theorem phase_eq_e (k n : ℕ) (α : ℝ) : phase k n α = e (α*(n : ℝ)^k) := by
  simp only [phase, e, mul_assoc]

/-- Rational polynomial phases are genuinely periodic in the summation
variable. Coprimality is unnecessary for this elementary fact. -/
theorem rational_monomial_periodic (k : ℕ) (a : ℤ) {q : ℕ} (hq : 0 < q) :
    Function.Periodic (fun n : ℕ => e ((a : ℝ)/q*(n : ℝ)^k)) q := by
  intro n
  have hmod : Int.ModEq (q : ℤ) ((n : ℤ)+(q : ℤ)) (n : ℤ) := Int.add_modEq_right
  obtain ⟨b,hb⟩ := (hmod.pow k).symm.dvd
  have hbr : ((n : ℝ)+(q : ℝ))^k - (n : ℝ)^k = (q : ℝ)*(b : ℝ) := by
    exact_mod_cast hb
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  have heq : (a : ℝ)/q*(n+q : ℕ)^k = (a : ℝ)/q*(n : ℝ)^k + ((a*b : ℤ) : ℝ) := by
    push_cast
    field_simp [hq0]
    congr 1
    linarith
  change e ((a : ℝ)/q*((n+q : ℕ) : ℝ)^k) = e ((a : ℝ)/q*(n : ℝ)^k)
  rw [heq, e_add_int]

/-- The conventional complete monomial sum, with representatives `1,...,q`. -/
def completeMonomialSum (k : ℕ) (a : ℤ) (q : ℕ) : ℂ :=
  ∑ n ∈ Finset.range q, e ((a : ℝ)/q*((n+1 : ℕ) : ℝ)^k)

/-- The ordinary monomial singular integral before scaling. -/
def monomialIntegral (k : ℕ) (P β : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..P, e (β*t^k)

theorem hasDerivAt_monomial_e (k : ℕ) (β t : ℝ) :
    HasDerivAt (fun x : ℝ => e (β*x^k))
      (e (β*t^k) * (((2*Real.pi*β*(k : ℝ)*t^(k-1) : ℝ) : ℂ)*Complex.I)) t := by
  have h := (((hasDerivAt_pow k t).const_mul (2*Real.pi*β)).ofReal_comp.mul_const Complex.I).cexp
  convert h using 1
  · funext x
    unfold e
    congr 1
    push_cast
    ring
  · unfold e
    congr 1
    · congr 1
      push_cast
      ring
    · push_cast
      ring

theorem deriv_monomial_e (k : ℕ) (β t : ℝ) :
    deriv (fun x : ℝ => e (β*x^k)) t =
      e (β*t^k) * (((2*Real.pi*β*(k : ℝ)*t^(k-1) : ℝ) : ℂ)*Complex.I) :=
  (hasDerivAt_monomial_e k β t).deriv

theorem continuous_deriv_monomial_e (k : ℕ) (β : ℝ) :
    Continuous (deriv (fun x : ℝ => e (β*x^k))) := by
  simp only [funext (deriv_monomial_e k β)]
  unfold e
  fun_prop

theorem norm_deriv_monomial_e_le (k : ℕ) (β : ℝ) {P t : ℝ}
    (ht : t ∈ Set.Icc 0 P) :
    ‖deriv (fun x : ℝ => e (β*x^k)) t‖ ≤ 2*Real.pi*|β| *(k : ℝ)*P^(k-1) := by
  rw [deriv_monomial_e, norm_mul, norm_e, one_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg Real.pi_pos.le,
    abs_of_nonneg (a := (k : ℝ)) (Nat.cast_nonneg k),
    abs_of_nonneg (a := t^(k-1)) (pow_nonneg ht.1 _)]
  gcongr
  · exact ht.1
  · exact ht.2

/-- Explicit ordinary narrow-major approximation. The complete sum and
integral are actual finite/Bochner expressions. At `q ≤ W` and
`|β| P^k ≤ W`, the error is `O_k(W²)`, with no epsilon loss. -/
theorem ordinary_rational_approximation (k : ℕ) (hk : 1 ≤ k) (a : ℤ)
    {q : ℕ} (hq : 0 < q) {P : ℝ} (hP : 0 ≤ P) (β : ℝ) :
    ‖ordinaryWeyl k P ((a : ℝ)/q+β) -
        (completeMonomialSum k a q/(q : ℂ))*monomialIntegral k P β‖ ≤
      3*q*(1+2*Real.pi*|β| *(k : ℝ)*P^k) := by
  have h := norm_positive_sum_sub_mean_integral_le hq
    (rational_monomial_periodic k a hq)
    (fun n => (norm_e _).le) (f := fun t => e (β*t^k))
    (B := 1) (D := 2*Real.pi*|β| *(k : ℝ)*P^(k-1)) hP
    (fun t => (hasDerivAt_monomial_e k β t).differentiableAt)
    (continuous_deriv_monomial_e k β) (norm_e _).le
    (fun t ht => norm_deriv_monomial_e_le k β ht)
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊P⌋₊,
      e (β*(n : ℝ)^k)*e ((a : ℝ)/q*(n : ℝ)^k)) =
      ordinaryWeyl k P ((a : ℝ)/q+β) := by
    unfold ordinaryWeyl ordinaryNumbers
    apply Finset.sum_congr rfl
    intro n _
    rw [phase_eq_e, ← e_add]
    congr 1
    ring
  have hpow : P*P^(k-1) = P^k := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  simpa only [hsum, periodicMean, completeMonomialSum, monomialIntegral,
    show P*(2*Real.pi*|β| *(k : ℝ)*P^(k-1)) =
      2*Real.pi*|β| *(k : ℝ)*P^k by rw [← hpow]; ring] using h

theorem norm_monomialIntegral_le (k : ℕ) {P : ℝ} (hP : 0 ≤ P) (β : ℝ) :
    ‖monomialIntegral k P β‖ ≤ P := by
  simpa only [monomialIntegral, sub_zero, abs_of_nonneg hP, one_mul] using
    intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
      (f := fun t : ℝ => e (β*t^k)) (a := 0) (b := P) (fun t _ => (norm_e _).le)

theorem norm_completeMonomialSum_div_le_one (k : ℕ) (a : ℤ)
    {q : ℕ} (hq : 0 < q) : ‖completeMonomialSum k a q/(q : ℂ)‖ ≤ 1 := by
  exact norm_periodicMean_le hq (fun n => (norm_e _).le)

theorem norm_ordinaryMajorModel_le (k : ℕ) (a : ℤ) {q : ℕ} (hq : 0 < q)
    {P : ℝ} (hP : 0 ≤ P) (β : ℝ) :
    ‖(completeMonomialSum k a q/(q : ℂ))*monomialIntegral k P β‖ ≤ P := by
  rw [norm_mul]
  exact (mul_le_mul (norm_completeMonomialSum_div_le_one k a hq)
    (norm_monomialIntegral_le k hP β) (norm_nonneg _) zero_le_one).trans_eq (one_mul P)

/-- Uniform approximation on the usual narrow major arcs. This is the
`O_k(W²)` input for replacing ordinary factors in the main-term integral. -/
theorem ordinary_narrow_major_approximation (k : ℕ) (hk : 1 ≤ k) (a : ℤ)
    {q : ℕ} (hq : 0 < q) {P W β : ℝ} (hP : 0 ≤ P)
    (hW : 1 ≤ W) (hqW : (q : ℝ) ≤ W) (hβ : |β| *P^k ≤ W) :
    ‖ordinaryWeyl k P ((a : ℝ)/q+β) -
        (completeMonomialSum k a q/(q : ℂ))*monomialIntegral k P β‖ ≤
      3*(1+2*Real.pi*(k : ℝ))*W^2 := by
  have hfac : 0 ≤ 2*Real.pi*(k : ℝ) := by positivity
  have hbound : 1+2*Real.pi*|β| *(k : ℝ)*P^k ≤
      (1+2*Real.pi*(k : ℝ))*W := by
    nlinarith [mul_le_mul_of_nonneg_left hβ hfac]
  calc
    _ ≤ 3*(q : ℝ)*(1+2*Real.pi*|β| *(k : ℝ)*P^k) :=
      ordinary_rational_approximation k hk a hq hP β
    _ ≤ 3*W*((1+2*Real.pi*(k : ℝ))*W) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hqW (by norm_num)) hbound
        (by positivity) (by positivity)
    _ = _ := by ring

theorem norm_pow_sub_pow_le {z w : ℂ} {P : ℝ}
    (hP : 0 ≤ P) (hz : ‖z‖ ≤ P) (hw : ‖w‖ ≤ P) (u : ℕ) :
    ‖z^u-w^u‖ ≤ (u : ℝ)*P^(u-1)*‖z-w‖ := by
  rw [← (Commute.all z w).geom_sum₂_mul u, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖∑ i ∈ Finset.range u, z^i*w^(u-1-i)‖ ≤
        ∑ i ∈ Finset.range u, ‖z^i*w^(u-1-i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range u, P^(u-1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ u-1 := by have := Finset.mem_range.mp hi; omega
      rw [norm_mul, norm_pow, norm_pow]
      calc
        _ ≤ P^i*P^(u-1-i) := mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz i)
          (pow_le_pow_left₀ (norm_nonneg w) hw _) (by positivity) (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; omega
    _ = _ := by simp

/-- Replacing the ordinary factors in an actual mixed Weyl product loses
one power of `P`, uniformly across a narrow major arc. -/
theorem mixed_ordinary_narrow_major_error (k u v : ℕ) (hk : 1 ≤ k)
    (hu : 1 ≤ u) (a : ℤ) {q : ℕ} (hq : 0 < q) {P W β R : ℝ}
    (hP : 0 ≤ P) (hW : 1 ≤ W) (hqW : (q : ℝ) ≤ W)
    (hβ : |β| *P^k ≤ W) :
    ‖ordinaryWeyl k P ((a : ℝ)/q+β)^u * smoothWeyl k P R ((a : ℝ)/q+β)^v -
      ((completeMonomialSum k a q/(q : ℂ))*monomialIntegral k P β)^u *
        smoothWeyl k P R ((a : ℝ)/q+β)^v‖ ≤
      3*(u : ℝ)*(1+2*Real.pi*(k : ℝ))*W^2*P^(u+v-1) := by
  rw [← sub_mul, norm_mul, norm_pow]
  have hpow := norm_pow_sub_pow_le hP (norm_ordinaryWeyl_le k ((a : ℝ)/q+β) hP)
    (norm_ordinaryMajorModel_le k a hq hP β) u
  have herr := ordinary_narrow_major_approximation k hk a hq hP hW hqW hβ
  have hsmooth : ‖smoothWeyl k P R ((a : ℝ)/q+β)‖^v ≤ P^v :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_smoothWeyl_le k R _ hP) v
  have hnonneg : 0 ≤ (u : ℝ)*P^(u-1) := by positivity
  calc
    _ ≤ ((u : ℝ)*P^(u-1)*(3*(1+2*Real.pi*(k : ℝ))*W^2))*P^v :=
      mul_le_mul (hpow.trans (mul_le_mul_of_nonneg_left herr hnonneg)) hsmooth
        (by positivity) (by positivity)
    _ = _ := by
      rw [show u+v-1 = (u-1)+v by omega, pow_add]
      ring

#print axioms norm_positive_sum_sub_mean_integral_le
#print axioms ordinary_rational_approximation
#print axioms ordinary_narrow_major_approximation
#print axioms mixed_ordinary_narrow_major_error

end Waring.EndgameCompletion
