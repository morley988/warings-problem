import Waring.ConditionalMoments
import Waring.FourthMomentSeed
import Waring.NinthFirstSeeds

/-!
# Published seed obligations begin at full moment order six

The zeroth, second and fourth moments are genuinely proved. The degree-nine
sixth and eighth moments are now also proved by the exact first-stage
iteration. The remaining source entries are explicit analytic obligations.
-/

noncomputable section
namespace Waring.Certificate
open Waring.SmoothMoments

def HighOrderAdmissibleCurve (k : ℕ) (c : Curve) : Prop :=
  ∀ i : ℕ, 3 ≤ i → i < c.size → AdmissibleExponent k (2*i) (c[i]!:ℝ)

/-- The still-unproved degree-nine source entries begin at full order ten. -/
def RemainingSource9Seeds : Prop :=
  ∀ i : ℕ, 5 ≤ i → i < source9.size → AdmissibleExponent 9 (2*i) (source9[i]!:ℝ)

theorem source9_high_of_remaining (h : RemainingSource9Seeds) :
    HighOrderAdmissibleCurve 9 source9 := by
  intro i hi hsize
  by_cases h5 : 5 ≤ i
  · exact h i h5 hsize
  have hcase : i=3 ∨ i=4 := by omega
  rcases hcase with rfl | rfl
  · exact NinthFirstSeeds.source9_entry_three
  · exact NinthFirstSeeds.source9_entry_four

def LowSeedShape (c : Curve) : Prop :=
  c[0]! = (0:Q) ∧ c[1]! = (1:Q) ∧ c[2]! = (2:Q)

instance (c : Curve) : Decidable (LowSeedShape c) := by
  unfold LowSeedShape
  infer_instance

theorem admissibleCurve_of_highOrder {k : ℕ} {c : Curve} (hk : 2 ≤ k)
    (hlow : LowSeedShape c) (hhigh : HighOrderAdmissibleCurve k c) :
    AdmissibleCurve k c := by
  intro i hi
  by_cases h3 : 3 ≤ i
  · exact hhigh i h3 hi
  · have hc : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases hc with rfl | rfl | rfl
    · simpa only [hlow.1,Rat.cast_zero,Nat.mul_zero] using admissibleExponent_zero k
    · simpa only [hlow.2.1,Rat.cast_one,Nat.mul_one] using
        admissibleExponent_two (show k≠0 by omega)
    · simpa only [hlow.2.2,Rat.cast_ofNat] using Waring.FourthMomentSeed.admissibleExponent_four hk

theorem source8_low_seeds : LowSeedShape source8 := by decide +kernel
theorem coefficientSource8_low_seeds : LowSeedShape coefficientSource8 := by decide +kernel
theorem source9_low_seeds : LowSeedShape source9 := by decide +kernel
theorem coefficientSource9_low_seeds : LowSeedShape coefficientSource9 := by decide +kernel

theorem source8_admissible_of_high (h : HighOrderAdmissibleCurve 8 source8) :
    AdmissibleCurve 8 source8 := admissibleCurve_of_highOrder (by norm_num) source8_low_seeds h

theorem coefficientSource8_admissible_of_high (h : HighOrderAdmissibleCurve 16 coefficientSource8) :
    AdmissibleCurve 16 coefficientSource8 :=
  admissibleCurve_of_highOrder (by norm_num) coefficientSource8_low_seeds h

theorem source9_admissible_of_high (h : HighOrderAdmissibleCurve 9 source9) :
    AdmissibleCurve 9 source9 := admissibleCurve_of_highOrder (by norm_num) source9_low_seeds h

theorem coefficientSource9_admissible_of_high (h : HighOrderAdmissibleCurve 18 coefficientSource9) :
    AdmissibleCurve 18 coefficientSource9 :=
  admissibleCurve_of_highOrder (by norm_num) coefficientSource9_low_seeds h

theorem final8_excesses_from_high_order_sources
    (hseed : HighOrderAdmissibleCurve 8 source8)
    (hcoefficientSeed : HighOrderAdmissibleCurve 16 coefficientSource8)
    (hsound : ∀ i, i < policies8.size → AnalyticPolicySound 8 policies8[i]!) :
    AdmissibleExcess 8 32 Waring.Endgame.delta8_32 ∧
    AdmissibleExcess 8 34 Waring.Endgame.delta8_34 :=
  final8_excesses_conditional (source8_admissible_of_high hseed)
    (coefficientSource8_admissible_of_high hcoefficientSeed) hsound

theorem final9_excesses_from_high_order_sources
    (hseed : HighOrderAdmissibleCurve 9 source9)
    (hcoefficientSeed : HighOrderAdmissibleCurve 18 coefficientSource9)
    (hsound : ∀ i, i < policies9.size → AnalyticPolicySound 9 policies9[i]!) :
    AdmissibleExcess 9 38 Waring.Endgame.delta9_38 ∧
    AdmissibleExcess 9 40 Waring.Endgame.delta9_40 :=
  final9_excesses_conditional (source9_admissible_of_high hseed)
    (coefficientSource9_admissible_of_high hcoefficientSeed) hsound

#print axioms source8_admissible_of_high
#print axioms final8_excesses_from_high_order_sources
#print axioms final9_excesses_from_high_order_sources

end Waring.Certificate
