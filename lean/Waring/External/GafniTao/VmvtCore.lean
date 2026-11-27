import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp

/-!
Minimal finite-count core for the MIT-0 smccolm/Lean VMVT port.
All definitions are identical to the pinned source definitions; the count
cardinality bridge below has a new elementary proof. The broad source imports
through classical Ford estimates and the prime number theorem are not used.
Source commit: bed45b21cb18f26f4d234422ebaa8b17e6624f05.
-/
open Finset
open scoped BigOperators ComplexConjugate
namespace GafniTao
noncomputable section

def fordRepresentationCount {β Γ : Type*} [DecidableEq β]
    [AddCommGroup Γ] [DecidableEq Γ]
    (B : Finset β) (F : β → Γ) (w : Γ) : ℕ :=
  ((B ×ˢ B).filter fun xy => F xy.1 - F xy.2 = w).card

abbrev FordVinogradovTuple (s Q : ℕ) := Fin s → Fin Q

/-- The vector `(∑ᵢ xᵢ, ..., ∑ᵢ xᵢ^k)` attached to a source tuple. -/
def fordVinogradovPowerVector (s k Q : ℕ) (x : FordVinogradovTuple s Q) :
    Fin k → ℤ :=
  fun j => ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ ((j : ℕ) + 1)

/-- Ford's shifted solution count `J_{s,k}(P; h)` with `Q = floor P`. -/
def fordVinogradovShiftedCountNat
    (s k Q : ℕ) (h : Fin k → ℤ) : ℕ :=
  fordRepresentationCount (Finset.univ : Finset (FordVinogradovTuple s Q))
    (fordVinogradovPowerVector s k Q) h

/-- The combinatorial form (1.4) of Ford's complete Vinogradov mean value. -/
def fordVinogradovMomentNat (s k Q : ℕ) : ℕ :=
  fordVinogradovShiftedCountNat s k Q 0

def fordVinogradovKappa (k : ℕ) : ℕ := k * (k + 1) / 2

theorem card_fordVinogradovTuple_univ (s Q : ℕ) :
    (Finset.univ : Finset (FordVinogradovTuple s Q)).card = Q ^ s := by
  simp [FordVinogradovTuple]

theorem fordVinogradovPowerVector_bounds
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) (j : Fin k) :
    (s : ℤ) ≤ fordVinogradovPowerVector s k Q x j ∧
      fordVinogradovPowerVector s k Q x j ≤
        (s : ℤ) * (Q : ℤ) ^ ((j : ℕ) + 1) := by
  let d : ℕ := (j : ℕ) + 1
  have htermLower (i : Fin s) :
      (1 : ℤ) ≤ ((x i : ℕ) + 1 : ℤ) ^ d := by
    apply one_le_pow₀
    omega
  have htermUpper (i : Fin s) :
      ((x i : ℕ) + 1 : ℤ) ^ d ≤ (Q : ℤ) ^ d := by
    have hbase : (x i : ℕ) + 1 ≤ Q := Nat.succ_le_iff.mpr (x i).isLt
    have hpow : ((x i : ℕ) + 1) ^ d ≤ Q ^ d := Nat.pow_le_pow_left hbase d
    exact_mod_cast hpow
  constructor
  · change (s : ℤ) ≤ ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d
    calc
      (s : ℤ) = ∑ _i : Fin s, (1 : ℤ) := by simp
      _ ≤ ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d :=
        Finset.sum_le_sum fun i _hi => htermLower i
  · change (∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d) ≤
      (s : ℤ) * (Q : ℤ) ^ d
    calc
      (∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d) ≤
          ∑ _i : Fin s, (Q : ℤ) ^ d :=
        Finset.sum_le_sum fun i _hi => htermUpper i
      _ = (s : ℤ) * (Q : ℤ) ^ d := by simp

abbrev FordPowerSolution (s k Q : ℕ) :=
  {xy : FordVinogradovTuple s Q × FordVinogradovTuple s Q //
    fordVinogradovPowerVector s k Q xy.1 = fordVinogradovPowerVector s k Q xy.2}

theorem card_fordPowerSolution (s k Q : ℕ) :
    Nat.card (FordPowerSolution s k Q) = fordVinogradovMomentNat s k Q := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [FordPowerSolution, fordVinogradovMomentNat,
    fordVinogradovShiftedCountNat, fordRepresentationCount, sub_eq_zero,
    ← Finset.univ_product_univ, Fintype.card_subtype]

def fordLambda34 (s k : ℕ) (delta : ℝ) : ℝ :=
  2 * (s : ℝ) - ((k : ℝ) * (k + 1)) / 2 + delta

def FordVinogradovMomentBound
    (s k : ℕ) (C delta : ℝ) : Prop :=
  ∀ Q : ℕ, 1 ≤ Q →
    (fordVinogradovMomentNat s k Q : ℝ) ≤
      C * (Q : ℝ) ^ fordLambda34 s k delta

def VinogradovCriticalEndpointTheorem : Prop :=
  ∀ (l : ℕ) (epsilon : ℝ), 1 ≤ l → 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧
      FordVinogradovMomentBound (fordVinogradovKappa l) l C epsilon

theorem fordVinogradovKappa_cast (l : ℕ) :
    (fordVinogradovKappa l : ℝ) =
      (l : ℝ) * ((l : ℝ) + 1) / 2 := by
  unfold fordVinogradovKappa
  rw [Nat.cast_div
    (even_iff_two_dvd.mp (Nat.even_mul_succ_self l))
    (by norm_num : (2 : ℝ) ≠ 0)]
  push_cast
  rfl


theorem ford_pow_mul_conj_pow (z : ℂ) (s : ℕ) :
    z ^ s * conj z ^ s = ((‖z‖ : ℝ) : ℂ) ^ (2 * s) := by
  rw [← mul_pow, Complex.mul_conj']
  rw [← pow_mul]

end
end GafniTao
