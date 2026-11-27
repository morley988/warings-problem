import Waring.SeedCompletionTerminalHolder
import Waring.PolicyCompletionNextDomain

/-!
# Exact mixed-moment Cauchy before each counted backward stage

The auxiliary family remains inside one complete sum. Cauchy is applied
before enlarging either finite domain. The shorter smooth variables at
frequency 2^k are then transported by the existing injective doubling map.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionCrossCauchy
open PolicyCompletionHolder SeedCompletionTerminalHolder SeedCompletionSharpBackward
open PolicyCompletionNextDomain PolicyCompletionCartesian
open SeedCompletionBackwardAggregate PolicyCompletionGoodRecurrence SmoothMoments

def frequencyCrossMoment {ι κ : Type*} (A : Finset ι) (f : ι → ℤ)
    (B : Finset κ) (g : κ → ℤ) (s : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ‖frequencySum A f x‖*‖frequencySum B g x‖^(2*s)

/-- Two independent finite frequency families, with the precise integer
relation required by the next backward row. -/
theorem frequencyCrossMoment_le_mixed {ι κ : Type*} (A : Finset ι) (f : ι → ℤ)
    (B : Finset κ) (g : κ → ℤ) (s u t : ℕ) (hut : u+t=2*s) :
    frequencyCrossMoment A f B g s ≤
      (mixedFrequencyEvenMoment A f 1 B g u)^(1/2 : ℝ)*
        (frequencyEvenMoment B g t)^(1/2 : ℝ) := by
  let F : ℝ → ℝ := fun x => ‖frequencySum A f x‖*‖frequencySum B g x‖^u
  let G : ℝ → ℝ := fun x => ‖frequencySum B g x‖^t
  have hF : Continuous F := (continuous_frequencySum A f).norm.mul
    ((continuous_frequencySum B g).norm.pow u)
  have hG : Continuous G := (continuous_frequencySum B g).norm.pow t
  have h := interval_product_powers_holder hF hG (fun _ => by dsimp [F]; positivity)
    (fun _ => by dsimp [G]; positivity) 1 1 2 2
    (t := 1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hleft (x : ℝ) : F x^1*G x^1 =
      ‖frequencySum A f x‖*‖frequencySum B g x‖^(2*s) := by
    dsimp [F,G]
    rw [pow_one,pow_one,mul_assoc,← pow_add,hut]
  have hfirst (x : ℝ) : F x^2 =
      ‖frequencySum A f x‖^2*‖frequencySum B g x‖^(2*u) := by
    dsimp [F]
    rw [mul_pow,← pow_mul,Nat.mul_comm u 2]
  have hsecond (x : ℝ) : G x^2=‖frequencySum B g x‖^(2*t) := by
    dsimp [G]
    rw [← pow_mul,Nat.mul_comm t 2]
  simpa only [hleft,hfirst,hsecond,show (1 : ℝ)-1/2=1/2 by norm_num,
    frequencyCrossMoment,mixedFrequencyEvenMoment,frequencyEvenMoment,frequencySum,mul_one] using h

theorem nextSmoothCrossIntegral_le_mixed {κ : Type*} (k s u t : ℕ)
    (hut : u+t=2*s) (C : Finset κ) (params : κ → List (ℤ × ℤ))
    (W : Finset ℕ) (N : ℤ) (Q R : ℝ) :
    nextSmoothCrossIntegral k s C params W N Q R ≤
      (nextSmoothMoment k u C params W N Q R)^(1/2 : ℝ)*
        (smoothMoment k (2*t) Q R)^(1/2 : ℝ) := by
  rw [nextSmoothCrossIntegral_eq,nextSmoothMoment_eq_mixed]
  have h := frequencyCrossMoment_le_mixed
    (aggregateNextDomain (C ×ˢ W) (fun p => (p.2 : ℤ)) N k)
    (aggregateNextPhase k (fun p => params p.1) (fun p => (p.2 : ℤ)))
    (smoothNumbers Q R) (fun n => (2 : ℤ)^k*((n^k : ℕ) : ℤ)) s u t hut
  rw [frequencyEvenMoment_mul_frequency _ _ t ((2 : ℤ)^k) (by positivity),
    ← smoothMoment_even_eq_frequency] at h
  simpa only [frequencyCrossMoment,Nat.cast_pow] using h

/-- The exact next-stage cross term is bounded through an actual Cartesian
mixed moment. Enlargement occurs only after the square is formed. -/
theorem nextSmoothCrossIntegral_le_cartesian {j : ℕ} (k s u t : ℕ)
    (hut : u+t=2*s) (H : Finset (Fin j → ℤ)) (C : Fin j → Finset ℤ)
    (W : Finset ℕ) (N T : ℤ) (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 2 ≤ R)
    (hT : ∀ w ∈ W,N/(w : ℤ)^k ≤ T) :
    nextSmoothCrossIntegral k s (integerCartesian H C)
      (fun c => integerParameters c.1 c.2) W N Q R ≤
      (cartesianMixedMoment k u (nextHeightSet H T) (nextCoefficientSets W C)
        1 (2*N) (smoothNumbers (2*Q) R) (fun n => (n : ℤ)^k))^(1/2 : ℝ)*
        (smoothMoment k (2*t) Q R)^(1/2 : ℝ) := by
  apply (nextSmoothCrossIntegral_le_mixed k s u t hut
    (integerCartesian H C) (fun c => integerParameters c.1 c.2) W N Q R).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (smoothMoment_nonneg ..) _)
  apply Real.rpow_le_rpow _ (nextSmoothMoment_le_cartesian_smooth k u H C W N T Q R hQ hR hT)
    (by norm_num)
  rw [nextSmoothMoment_eq_mixed,mixedFrequencyEvenMoment_eq_card]
  positivity

#print axioms frequencyCrossMoment_le_mixed
#print axioms nextSmoothCrossIntegral_le_cartesian
end Waring.SeedCompletionCrossCauchy
