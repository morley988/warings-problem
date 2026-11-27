import Waring.SampledQuadraticSecondAsymptotic

/-!
# The quadratic second-moment resource below the exact minor-height threshold

The actual auxiliary arcs allow an R-power loss in the height lower bound.
We retain that loss explicitly, then absorb it using one sufficiently small
positive smoothness exponent. The linear modulation is common to all samples.
-/

noncomputable section
open scoped BigOperators
namespace Waring.NormalizedQuadratic
open RationalHeight SampledQuadraticSecond SampledQuadraticSecondAsymptotic

/-- A fixed multiplier and a height loss P^kappa cost at most P^kappa. -/
theorem sampled_second_height_loss_log (S : Finset ℤ) (α t D P κ : ℝ)
    (c H : ℕ) (hc : 0 < c) (hκ : 0 ≤ κ)
    (hS : ∀ z ∈ S, |(z : ℝ)| ≤ P) (hD : 0 ≤ D)
    (hdiv : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ P^2 → (n.divisors.card : ℝ) ≤ D)
    (hP : 1 ≤ P) (hPH : P ≤ (H : ℝ))
    (hPL : P^(1-κ) ≤ height ((H : ℝ)*P^2) α) :
    sampledMoment S ((c : ℝ)*α) t H ≤
      (6+1024*D*((c : ℝ)+3)*DyadicLogLoss.logLoss (H : ℝ))*P^κ*P*H := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hHpos : (0 : ℝ) < H := hPpos.trans_le hPH
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hpow : 1 ≤ P^κ := Real.one_le_rpow hP hκ
  have hpow0 : 0 ≤ P^κ := Real.rpow_nonneg hPpos.le κ
  have hfloor : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le hPpos.le
  have hdiv' : ∀ n : ℕ, 0 < n → n ≤ ⌊P⌋₊^2 → (n.divisors.card : ℝ) ≤ D := by
    intro n hn hnM
    apply hdiv n hn
    have hcast : (n : ℝ) ≤ (⌊P⌋₊ : ℝ)^2 := by exact_mod_cast hnM
    nlinarith [show (0 : ℝ) ≤ (⌊P⌋₊ : ℝ) by positivity]
  have hheight : P ≤ ((c : ℝ)*P^κ)*height ((H : ℝ)*P^2) ((c : ℝ)*α) := by
    calc
      P = P^κ*P^(1-κ) := by rw [← Real.rpow_add hPpos]; ring_nf; rw [Real.rpow_one]
      _ ≤ P^κ*height ((H : ℝ)*P^2) α := mul_le_mul_of_nonneg_left hPL hpow0
      _ ≤ P^κ*((c : ℝ)*height ((H : ℝ)*P^2) ((c : ℝ)*α)) :=
        mul_le_mul_of_nonneg_left (height_mul_phase_lower (by positivity) hc) hpow0
      _ = _ := by ring
  have hb := sampledMoment_minor_height_log S ((c : ℝ)*α) t D P ((c : ℝ)*P^κ)
    H ⌊P⌋₊ (centered_subset_floor S P hS) hD hdiv' hP hfloor hPH
    (one_le_mul_of_one_le_of_one_le hc1 hpow) hheight
  have hlog0 : 0 ≤ DyadicLogLoss.logLoss (H : ℝ) :=
    DyadicLogLoss.logLoss_nonneg (hP.trans hPH)
  have hs : (c : ℝ)*P^κ+3 ≤ ((c : ℝ)+3)*P^κ := by nlinarith only [hpow]
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 1024*D*DyadicLogLoss.logLoss (H : ℝ) by positivity)
  have hcoef : 6+1024*D*((c : ℝ)*P^κ+3)*DyadicLogLoss.logLoss (H : ℝ) ≤
      (6+1024*D*((c : ℝ)+3)*DyadicLogLoss.logLoss (H : ℝ))*P^κ := by
    nlinarith only [hpow,hm]
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hPpos.le) hHpos.le)

theorem sampled_second_height_loss_epsilon (A : ℝ) (hA : 0 ≤ A) (c : ℕ) (hc : 0 < c)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ H : ℕ,
      P ≤ (H : ℝ) → (H : ℝ) ≤ P^A → ∀ α t κ : ℝ, 0 ≤ κ → ∀ S : Finset ℤ,
      (∀ z ∈ S, |(z : ℝ)| ≤ P) →
      P^(1-κ) ≤ RationalHeight.height ((H : ℝ)*P^2) α →
      SampledQuadraticSecond.sampledMoment S ((c : ℝ)*α) t H ≤
        C*P^(1+ε+κ)*H := by
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Cd, hCd, hdiv⟩ := DivisorBound.divisor_count_le_cutoff_rpow hδ
  obtain ⟨Cl, hCl, hlog⟩ := DyadicLogLoss.logLoss_pow_le_rpow 1 (half_pos hε)
  let K := Cd*(A+1)*Cl
  let C := 6+1024*((c : ℝ)+3)*K
  have hA1 : 0 < A+1 := by linarith
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro P hP H hPH hHA α t κ hκ S hS hPL
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hHpos : (0 : ℝ) < H := hPpos.trans_le hPH
  have hP2 : 1 ≤ P^2 := by nlinarith
  let D := Cd*(P^2)^δ
  have hD : 0 < D := by dsimp [D]; positivity
  have hdivD : ∀ n : ℕ, 0 < n → (n : ℝ) ≤ P^2 → (n.divisors.card : ℝ) ≤ D :=
    fun n hn hnP => hdiv (P^2) hP2 n hn hnP
  have hDpow : D = Cd*P^(ε/2) := by
    dsimp [D]
    rw [← Real.rpow_natCast P 2, ← Real.rpow_mul hPpos.le]
    norm_num only [Nat.cast_ofNat]
    have heq : (2 : ℝ)*δ = ε/2 := by dsimp [δ]; ring
    rw [heq]
  have hFH : DyadicLogLoss.logLoss (H : ℝ) ≤ (A+1)*Cl*P^(ε/2) := by
    have hb := logLoss_polynomial_range hP hHpos hA hHA
    have hp : DyadicLogLoss.logLoss P ≤ Cl*P^(ε/2) := by simpa using hlog P hP
    have hm := mul_le_mul_of_nonneg_left hp hA1.le
    exact hb.trans (by simpa only [mul_assoc] using hm)
  have hprod : D*DyadicLogLoss.logLoss (H : ℝ) ≤ K*P^ε := by
    calc
      D*DyadicLogLoss.logLoss (H : ℝ) ≤ D*((A+1)*Cl*P^(ε/2)) :=
        mul_le_mul_of_nonneg_left hFH hD.le
      _ = K*(P^(ε/2)*P^(ε/2)) := by rw [hDpow]; dsimp [K]; ring
      _ = K*P^ε := by
        rw [← Real.rpow_add hPpos]
        congr 2
        ring
  have hPeps : 1 ≤ P^ε := Real.one_le_rpow hP hε.le
  have hcoeff : 6+1024*D*((c : ℝ)+3)*DyadicLogLoss.logLoss (H : ℝ) ≤ C*P^ε := by
    have hm := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ 1024*((c : ℝ)+3) by positivity)
    dsimp [C]
    nlinarith
  have hb := sampled_second_height_loss_log
    S α t D P κ c H hc hκ hS hD.le hdivD hP hPH hPL
  calc
    SampledQuadraticSecond.sampledMoment S ((c : ℝ)*α) t H ≤
        (6+1024*D*((c : ℝ)+3)*DyadicLogLoss.logLoss (H : ℝ))*P^κ*P*H := hb
    _ ≤ (C*P^ε)*P^κ*P*H :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hPpos.le κ)) hPpos.le) hHpos.le
    _ = C*P^(1+ε+κ)*H := by rw [Real.rpow_add hPpos, Real.rpow_add hPpos, Real.rpow_one]; ring

/-- The actual normalized centered second moment. -/
def normalizedSecond (S : Finset ℤ) (P α t : ℝ) (c H : ℕ) : ℝ :=
  sampledMoment S ((c : ℝ)*α) t H / ((H : ℝ)*P^2)

/-- The original auxiliary-arc height loss P/R^rho is absorbed uniformly.
The resulting normalized saving is exactly one, with arbitrary epsilon. -/
theorem normalized_second_of_smooth_height (A rho : ℝ) (hA : 0 ≤ A) (hrho : 0 ≤ rho)
    (c : ℕ) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ P : ℝ, 1 ≤ P → ∀ R : ℝ, 1 ≤ R → R ≤ P^η →
      ∀ H : ℕ, P ≤ (H : ℝ) → (H : ℝ) ≤ P^A →
      ∀ α t : ℝ, ∀ S : Finset ℤ, (∀ z ∈ S, |(z : ℝ)| ≤ P) →
      P/R^rho ≤ height ((H : ℝ)*P^2) α →
      normalizedSecond S P α t c H ≤ C*P^(ε-1) := by
  let η := ε/(2*(rho+1))
  have hη : 0 < η := by dsimp [η]; positivity
  have hκ : 0 ≤ rho*η := mul_nonneg hrho hη.le
  have hκloss : rho*η ≤ ε/2 := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2*(rho+1))).mpr
    nlinarith only [hε,hrho]
  obtain ⟨C,hC,hbound⟩ := sampled_second_height_loss_epsilon A hA c hc (half_pos hε)
  refine ⟨η,C,hη,hC,?_⟩
  intro P hP R hR hRup H hPH hHA α t S hS hPL
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hHpos : (0 : ℝ) < H := hPpos.trans_le hPH
  have hLpos := height_pos ((H : ℝ)*P^2) α
  have hRpow : R^rho ≤ P^(rho*η) := by
    calc
      _ ≤ (P^η)^rho := Real.rpow_le_rpow hRpos.le hRup hrho
      _ = _ := by rw [← Real.rpow_mul hPpos.le]; congr 1; ring
  have hPL' : P^(1-rho*η) ≤ height ((H : ℝ)*P^2) α := by
    have hp := (div_le_iff₀ (Real.rpow_pos_of_pos hRpos rho)).mp hPL
    have hp' : P ≤ height ((H : ℝ)*P^2) α * P^(rho*η) :=
      hp.trans (mul_le_mul_of_nonneg_left hRpow hLpos.le)
    rw [Real.rpow_sub hPpos, Real.rpow_one]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hPpos _)).mpr hp'
  have hb := hbound P hP H hPH hHA α t (rho*η) hκ S hS hPL'
  unfold normalizedSecond
  apply (div_le_iff₀ (by positivity : 0 < (H : ℝ)*P^2)).mpr
  calc
    _ ≤ C*P^(1+ε/2+rho*η)*H := hb
    _ ≤ C*P^(1+ε)*H := by
      apply mul_le_mul_of_nonneg_right _ hHpos.le
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hP (by linarith)) hC.le
    _ = (C*P^(ε-1))*((H : ℝ)*P^2) := by
      rw [← Real.rpow_natCast P 2]
      have hid : P^(ε-1)*P^(2:ℝ) = P^(1+ε) := by
        rw [← Real.rpow_add hPpos]
        congr 1
        ring
      calc
        _ = C*(P^(1+ε))*(H : ℝ) := rfl
        _ = C*(P^(ε-1)*P^(2:ℝ))*(H : ℝ) := by rw [hid]
        _ = _ := by norm_num only [Nat.cast_ofNat]; ring

#print axioms sampled_second_height_loss_log
#print axioms sampled_second_height_loss_epsilon
#print axioms normalized_second_of_smooth_height
end Waring.NormalizedQuadratic
