import Waring.SeedCompletionScaleAlgebra
import Waring.SeedCompletionSecondTransport
import Waring.SeedCompletionNinthSecondFourthSource

/-! # Literal second-stage domains at fixed power scales -/
noncomputable section
namespace Waring.SeedCompletionSecondScales
open SmoothMoments SeedCompletionSourceBounds SeedCompletionSecondTransport
open PolicyCompletionHolder SeedCompletionInitialMixed SeedCompletionBackwardAggregate
open SeedCompletionSharpBackward CoefficientPower

def secondMoment (k r : ℕ) (φ₁ φ₂ P R : ℝ) : ℝ :=
  frequencyEvenMoment (secondDomain (2*P) (P^(1-(k : ℝ)*φ₁))
    (2*P^(1-(k : ℝ)*φ₂)) (2*P) R (P^φ₁) (P^φ₂)) (secondPhase k) r

def firstMixed (k u : ℕ) (φ₁ P R : ℝ) : ℝ :=
  PolicyCompletionFundamental.sourceMixedMoment k u
    (firstLabels (P^(1-(k : ℝ)*φ₁)) P R (P^φ₁)) firstParameters (firstCenters P)
    (2*P^(1-φ₁)) R

def secondCross (k u : ℕ) (φ₁ φ₂ P R : ℝ) : ℝ :=
  nextSmoothCrossIntegral k u
    (firstLabels (P^(1-(k : ℝ)*φ₁)) P R (P^φ₁)) firstParameters
    (coefficientBlock (2*P^(1-φ₁)) R (P^φ₂)) (⌊2*P⌋₊ : ℤ)
    (2*P^(1-φ₁-φ₂)) R

theorem secondMoment_nonneg (k r : ℕ) (φ₁ φ₂ P R : ℝ) :
    0 ≤ secondMoment k r φ₁ φ₂ P R := by
  unfold secondMoment
  rw [frequencyEvenMoment_eq_card]
  positivity

theorem secondCross_nonneg (k u : ℕ) (φ₁ φ₂ P R : ℝ) :
    0 ≤ secondCross k u φ₁ φ₂ P R := nextSmoothCrossIntegral_nonneg ..

/-- Normalize a proved literal terminal bound. Its displayed parameter
range is preserved; constants from the enlarged center and new height do
not change the exponent. -/
theorem second_source_power_of_terminal {k r j : ℕ} {d T ρ φ₁ φ₂ : ℝ}
    (hk : 0 < k) (hT : 0 < T) (hρ : 0 < ρ)
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/(k : ℝ))
    (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/(k : ℝ))
    (hsource : ∀ ε : ℝ,0 < ε → ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧
      ∀ P : ℝ,P₀ ≤ P → ∀ H₁ H₂ Q R M₁ M₂ : ℝ,
      1 ≤ H₁ → H₁ ≤ P → 1 ≤ H₂ → H₂ ≤ P →
      1 ≤ M₁ → M₁ ≤ P^(1/(k : ℝ)) → 1 ≤ M₂ → M₂ ≤ P^(1/(k : ℝ)) →
      1 ≤ R → R ≤ P^(min (ε/T) ρ) →
      frequencyEvenMoment (secondDomain P H₁ H₂ Q R M₁ M₂) (secondPhase k) r ≤
        C*P^(d+ε)*H₁^j*H₂^j*M₁^j*M₂^j) :
    SourcePowerBound (secondMoment k r φ₁ φ₂)
      (d+(j : ℝ)*(2+(1-(k : ℝ))*(φ₁+φ₂))) := by
  intro ε hε
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ := hsource ε hε
  refine ⟨min (ε/T) ρ,lt_min (div_pos hε hT) hρ,?_⟩
  intro η hη hηle
  refine ⟨C*2^(d+ε)*(2 : ℝ)^j,by positivity,P₀,hP₀,?_⟩
  intro P hPP
  have hP : 1 ≤ P := hP₀.trans hPP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hP2 : P ≤ 2*P := by linarith
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hφ₁mul : φ₁*(k : ℝ) ≤ 1 := (le_div_iff₀ hkpos).mp hφ₁k
  have hφ₂mul : φ₂*(k : ℝ) ≤ 1 := (le_div_iff₀ hkpos).mp hφ₂k
  have hH₁ : 1 ≤ P^(1-(k : ℝ)*φ₁) := Real.one_le_rpow hP (by nlinarith)
  have hH₂ : 1 ≤ P^(1-(k : ℝ)*φ₂) := Real.one_le_rpow hP (by nlinarith)
  have hH₁P : P^(1-(k : ℝ)*φ₁) ≤ P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP
      (show 1-(k : ℝ)*φ₁ ≤ 1 by nlinarith [mul_nonneg hkpos.le hφ₁])
  have hH₂P : P^(1-(k : ℝ)*φ₂) ≤ P := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP
      (show 1-(k : ℝ)*φ₂ ≤ 1 by nlinarith [mul_nonneg hkpos.le hφ₂])
  have hM₁ : 1 ≤ P^φ₁ := Real.one_le_rpow hP hφ₁
  have hM₂ : 1 ≤ P^φ₂ := Real.one_le_rpow hP hφ₂
  have hM₁P : P^φ₁ ≤ (2*P)^(1/(k : ℝ)) :=
    (Real.rpow_le_rpow_of_exponent_le hP hφ₁k).trans
      (Real.rpow_le_rpow hPp.le hP2 (by positivity))
  have hM₂P : P^φ₂ ≤ (2*P)^(1/(k : ℝ)) :=
    (Real.rpow_le_rpow_of_exponent_le hP hφ₂k).trans
      (Real.rpow_le_rpow hPp.le hP2 (by positivity))
  have hR : 1 ≤ P^η := Real.one_le_rpow hP hη.le
  have hRP : P^η ≤ (2*P)^(min (ε/T) ρ) :=
    (Real.rpow_le_rpow_of_exponent_le hP hηle).trans
      (Real.rpow_le_rpow hPp.le hP2 (le_min (by positivity) hρ.le))
  have hb := hbound (2*P) (hPP.trans hP2)
    (P^(1-(k : ℝ)*φ₁)) (2*P^(1-(k : ℝ)*φ₂)) (2*P) (P^η) (P^φ₁) (P^φ₂)
    hH₁ (hH₁P.trans hP2) (by linarith) (by linarith)
    hM₁ hM₁P hM₂ hM₂P hR hRP
  rw [abs_of_nonneg (secondMoment_nonneg ..)]
  apply hb.trans_eq
  have hp (a : ℝ) : (P^a)^j=P^(a*(j : ℝ)) :=
    (Real.rpow_mul_natCast hPp.le a j).symm
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hPp.le,mul_pow]
  simp_rw [hp]
  calc
    _ = (C*2^(d+ε)*(2 : ℝ)^j)*
        (P^(d+ε)*P^((1-(k : ℝ)*φ₁)*(j : ℝ))*P^((1-(k : ℝ)*φ₂)*(j : ℝ))*
          P^(φ₁*(j : ℝ))*P^(φ₂*(j : ℝ))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hPp,← Real.rpow_add hPp,← Real.rpow_add hPp,← Real.rpow_add hPp]
      congr 2
      ring

theorem ninth_second_power {φ₁ φ₂ : ℝ}
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/9)
    (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/9) :
    SourcePowerBound (secondMoment 9 1 φ₁ φ₂) (3-8*(φ₁+φ₂)) := by
  have H := second_source_power_of_terminal (k := 9) (r := 1) (j := 1) (d := 1)
    (T := 4) (ρ := 7/18) (by norm_num) (by norm_num) (by norm_num)
    hφ₁ (by norm_num; exact hφ₁k) hφ₂ (by norm_num; exact hφ₂k) ?_
  · convert H using 1 <;> norm_num <;> ring
  intro ε hε
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ :=
    SeedCompletionNinthDoubleSource.source_ninth_second_second_moment hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₁P hM₂ hM₂P hR hRP
  simpa only [frequencyEvenMoment,show 2*1=2 by norm_num,pow_one] using
    hbound P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₁P hM₂ hM₂P hR hRP

theorem ninth_fourth_power {φ₁ φ₂ : ℝ}
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/9)
    (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/9) :
    SourcePowerBound (secondMoment 9 2 φ₁ φ₂) (8-24*(φ₁+φ₂)) := by
  have H := second_source_power_of_terminal (k := 9) (r := 2) (j := 3) (d := 2)
    (T := 12) (ρ := 1/24) (by norm_num) (by norm_num) (by norm_num)
    hφ₁ (by norm_num; exact hφ₁k) hφ₂ (by norm_num; exact hφ₂k) ?_
  · convert H using 1 <;> norm_num <;> ring
  intro ε hε
  obtain ⟨C,hC,P₀,hP₀,hbound⟩ :=
    SeedCompletionNinthSecondFourthSource.source_ninth_second_fourth_moment hε
  refine ⟨C,hC,P₀,hP₀,?_⟩
  intro P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₁P hM₂ hM₂P hR hRP
  simpa only [frequencyEvenMoment,show 2*2=4 by norm_num] using
    hbound P hPP H₁ H₂ Q R M₁ M₂ hH₁ hH₁P hH₂ hH₂P hM₁ hM₁P hM₂ hM₂P hR hRP

#print axioms ninth_second_power
#print axioms ninth_fourth_power
end Waring.SeedCompletionSecondScales
