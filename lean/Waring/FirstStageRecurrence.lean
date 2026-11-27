import Waring.FirstStageTransport
import Waring.IntegerDifferenceSize

/-!
# A proved recurrence for pure smooth moments

The first source stage is specialized to the actual smooth summation set.
All derivative, center-cardinality and coefficient-cardinality conditions
are discharged. The remaining cross integral is the literal one to which
the second- or fourth-moment terminal applies.
-/

noncomputable section
open scoped BigOperators
namespace Waring.FirstStageTransport
open SmoothMoments IntegerDifferencePolynomial FirstDifferenceSecond
open PolicyCompletionFundamental PolicyCompletionGoodBranch
open SeedCompletionSharpBackward SeedCompletionTerminalHolder
open SeedCompletionBackwardAggregate

theorem frequencyEvenMoment_nonneg {ι : Type*} (A : Finset ι) (f : ι → ℤ) (r : ℕ) :
    0 ≤ frequencyEvenMoment A f r := by
  rw [frequencyEvenMoment_eq_card]
  positivity

def firstCross (k s : ℕ) (P R M : ℝ) : ℝ :=
  nextSmoothCrossIntegral k s ({()} : Finset Unit) (fun _ => [])
    (CoefficientPower.coefficientBlock P R M) (⌊P⌋₊ : ℤ) (P/M) R

theorem firstCross_nonneg (k s : ℕ) (P R M : ℝ) :
    0 ≤ firstCross k s P R M := nextSmoothCrossIntegral_nonneg ..

theorem firstCross_le_source_second (k s : ℕ) {P R M : ℝ}
    (hP : 1 ≤ P) (hM : 1 ≤ M) :
    firstCross k s P R M ≤
      (frequencyEvenMoment (sourceFirstDomain P (P/M^k) P R M) (firstFrequency k) 1)^
        (1/2 : ℝ) * (smoothMoment k (4*s) (P/M) R)^(1/2 : ℝ) := by
  apply (nextSmoothCrossIntegral_le_second k s ({()} : Finset Unit) (fun _ => [])
    (CoefficientPower.coefficientBlock P R M) (⌊P⌋₊ : ℤ) (P/M) R).trans
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow
    (frequencyEvenMoment_nonneg _ _ _) (initial_auxiliary_le_source k 1 hP hM)
    (by norm_num)) (Real.rpow_nonneg (smoothMoment_nonneg ..) _)

theorem firstCross_le_source_fourth (k : ℕ) {P R M : ℝ}
    (hP : 1 ≤ P) (hM : 1 ≤ M) :
    firstCross k 3 P R M ≤
      (frequencyEvenMoment (sourceFirstDomain P (P/M^k) P R M) (firstFrequency k) 2)^
        (1/4 : ℝ) * (smoothMoment k 8 (P/M) R)^(3/4 : ℝ) := by
  apply (nextSmoothCrossIntegral_le_fourth k ({()} : Finset Unit) (fun _ => [])
    (CoefficientPower.coefficientBlock P R M) (⌊P⌋₊ : ℤ) (P/M) R).trans
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow
    (frequencyEvenMoment_nonneg _ _ _) (initial_auxiliary_le_source k 2 hP hM)
    (by norm_num)) (Real.rpow_nonneg (smoothMoment_nonneg ..) _)

theorem initialCenters_card_le {P R : ℝ} (hP : 0 ≤ P) :
    ((initialCenters P R).card : ℝ) ≤ P := by
  calc
    _ ≤ ((smoothNumbers P R).card : ℝ) := by
      exact_mod_cast Finset.card_image_le
    _ ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast smoothNumbers_card_le P R
    _ ≤ P := Nat.floor_le hP

theorem coefficientBlock_card_le {P R M : ℝ} (hMR : 0 ≤ M*R) :
    ((CoefficientPower.coefficientBlock P R M).card : ℝ) ≤ M*R := by
  calc
    _ ≤ ((smoothNumbers (M*R) R).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (CoefficientPower.coefficientBlock_subset P R M)
    _ ≤ (⌊M*R⌋₊ : ℝ) := by exact_mod_cast smoothNumbers_card_le (M*R) R
    _ ≤ M*R := Nat.floor_le hMR

/-- A literal pure smooth-moment recurrence. Its only non-numerical quantity
beyond the lower smooth moment is the actual first cross integral. -/
theorem first_stage_recurrence (k s : ℕ) (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ R M : ℝ, 1 ≤ R → 1 ≤ M →
      smoothMoment k (2*(s+2)) P R ≤ C *
        (M*P^(1+ε)*smoothMoment k (2*(s+1)) P R +
          P^(1+ε)*(M*R)^(2*(s+1))*smoothMoment k (2*(s+1)) (P/M) R +
          P^ε*(M*R)^(2*s+1)*firstCross k (s+1) P R M) := by
  let B : ℝ := ((k+1)*(k-1)+1 : ℕ)
  obtain ⟨P₀,hP₀,hsize⟩ := derivative_magnitude_polynomial_bound k k
  obtain ⟨Cb,hCb,Cg,hCg,hrec⟩ := source_fundamental_sharp (κ := Unit) k
    (B := B) (by dsimp [B]; positivity) hε
  let d : ℝ := ((k-1 : ℕ) : ℝ)^2 + ((s : ℝ)+1)*Cb
  let D : ℝ := d+2*Cg+1
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨((s : ℝ)+3)*D,by positivity,P₀,hP₀,?_⟩
  intro P hPP₀ R M hR hM
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hMP : 1 ≤ M*P^(1+ε) := by
    have hp := Real.one_le_rpow hP (show 0 ≤ 1+ε by linarith)
    nlinarith
  have hderiv : ∀ a ∈ ({()} : Finset Unit) ×ˢ initialCenters P R,
      (derivativeMagnitude (fun _ : Unit => powerPolynomial k []) a : ℝ) ≤ P^B := by
    intro a ha
    have hz := (Finset.mem_product.mp ha).2
    obtain ⟨n,hn,heq⟩ := Finset.mem_image.mp hz
    have hb := (mem_smoothNumbers.mp hn).1
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    apply hsize P hPP₀ [] (by simp) (by simp) (by simp) a.2
    rw [← heq,Int.cast_natCast,abs_of_nonneg hn0]
    exact (Nat.cast_le.mpr hb.2).trans (Nat.floor_le hPpos.le)
  have H := hrec ({()} : Finset Unit) (fun _ => []) (by simp)
    (by simpa using hk) (⌊P⌋₊ : ℤ) (initialCenters P R) (initialCenters_subset P R)
    P P R M hP le_rfl hM hderiv s
  rw [initial_sourceMixedMoment,initial_sourceMixedMoment] at H
  simp only [Finset.card_singleton,Nat.cast_one,one_mul,mul_one] at H
  change smoothMoment k (2*(s+1+1)) P R ≤
    ((s : ℝ)+3)*(_+_+Cg*P^ε*((CoefficientPower.coefficientBlock P R M).card : ℝ)^
      (2*(s+1)-1) *
      (((CoefficientPower.coefficientBlock P R M).card : ℝ)*
        ((initialCenters P R).card : ℝ)*smoothMoment k (2*(s+1)) (P/M) R +
        2*firstCross k (s+1) P R M)) at H
  have hW := coefficientBlock_card_le (P := P) (mul_nonneg hMpos.le hRpos.le)
  have hZ := initialCenters_card_le (R := R) hPpos.le
  have hJ := smoothMoment_nonneg k (2*(s+1)) P R
  have hJ' := smoothMoment_nonneg k (2*(s+1)) (P/M) R
  have hX := firstCross_nonneg k (s+1) P R M
  have hpow : P^(1+ε)=P*P^ε := by rw [Real.rpow_add hPpos,Real.rpow_one]
  have hzterm : ((k-1 : ℕ) : ℝ)^2*smoothMoment k (2*(s+1)) P R ≤
      ((k-1 : ℕ) : ℝ)^2*(M*P^(1+ε)*smoothMoment k (2*(s+1)) P R) := by
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left hJ hMP) (sq_nonneg _)
  have hblock : Cg*P^ε*((CoefficientPower.coefficientBlock P R M).card : ℝ)^
        (2*(s+1)-1) *
        (((CoefficientPower.coefficientBlock P R M).card : ℝ)*
          ((initialCenters P R).card : ℝ)*smoothMoment k (2*(s+1)) (P/M) R +
          2*firstCross k (s+1) P R M) ≤
      Cg*P^ε*(M*R)^(2*s+1)*
        (M*R*P*smoothMoment k (2*(s+1)) (P/M) R+2*firstCross k (s+1) P R M) := by
    rw [show 2*(s+1)-1=2*s+1 by omega]
    gcongr
  have hrough : smoothMoment k (2*(s+2)) P R ≤ ((s : ℝ)+3)*
      (d*(M*P^(1+ε)*smoothMoment k (2*(s+1)) P R)+
        Cg*(P^(1+ε)*(M*R)^(2*(s+1))*smoothMoment k (2*(s+1)) (P/M) R)+
        (2*Cg)*(P^ε*(M*R)^(2*s+1)*firstCross k (s+1) P R M)) := by
    apply H.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ ((k-1 : ℕ) : ℝ)^2*(M*P^(1+ε)*smoothMoment k (2*(s+1)) P R)+
          ((s : ℝ)+1)*(Cb*M*P*P^ε*smoothMoment k (2*(s+1)) P R)+
          Cg*P^ε*(M*R)^(2*s+1)*
            (M*R*P*smoothMoment k (2*(s+1)) (P/M) R+2*firstCross k (s+1) P R M) :=
        add_le_add (add_le_add_right hzterm _) hblock
      _ = _ := by
        rw [show 2*(s+1)=(2*s+1)+1 by omega,pow_succ,hpow]
        dsimp only [d]
        ring
  apply hrough.trans
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hdD : d ≤ D := by dsimp [D]; linarith
  have hCgD : Cg ≤ D := by dsimp [D]; linarith
  have h2CgD : 2*Cg ≤ D := by dsimp [D]; linarith
  have hcomb {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      d*a+Cg*b+(2*Cg)*c ≤ D*(a+b+c) := by
    have h₁ := mul_le_mul_of_nonneg_right hdD ha
    have h₂ := mul_le_mul_of_nonneg_right hCgD hb
    have h₃ := mul_le_mul_of_nonneg_right h2CgD hc
    nlinarith
  exact hcomb (by positivity) (by positivity) (by positivity)

#print axioms first_stage_recurrence
#print axioms firstCross_le_source_second
#print axioms firstCross_le_source_fourth
end Waring.FirstStageTransport
