import Waring.EndgameCompletionPrimePowerBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergent local Euler coefficients

Positive levels are indexed by `u*k+v`, `1≤v≤k`.  The proved prime-power
bounds therefore reduce every local coefficient series to a finite sum
of geometric series, including the exceptional primes in degrees eight
and nine.
-/

noncomputable section

open scoped BigOperators

namespace Waring.EndgameCompletion

theorem summable_tail_of_block_bound (f : ℕ → ℝ) (k : ℕ) (hk : 0 < k)
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hf : ∀ n, 0 ≤ f n)
    (hbound : ∀ (u : ℕ) (v : Fin k), f (u*k+(v.val+1)) ≤ C*ρ^u) :
    Summable (fun l => f (l+1)) ∧
      (∑' l : ℕ, f (l+1)) ≤ (k : ℝ)*C/(1-ρ) := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hgeom := summable_geometric_of_lt_one hρ0 hρ1
  have hmajor : Summable (fun x : ℕ × Fin k => C*ρ^x.1) := by
    simpa only [mul_comm] using hgeom.mul_of_nonneg
      (hasSum_fintype (fun _ : Fin k => C)).summable (fun _ => pow_nonneg hρ0 _) (fun _ => hC)
  have hbound' (x : ℕ × Fin k) : f ((Nat.divModEquiv k).symm x+1) ≤ C*ρ^x.1 := by
    simpa only [Nat.divModEquiv_symm_apply, Nat.add_assoc] using hbound x.1 x.2
  have hpair : Summable (fun x : ℕ × Fin k => f ((Nat.divModEquiv k).symm x+1)) :=
    Summable.of_nonneg_of_le (fun _ => hf _) hbound' hmajor
  refine ⟨((Nat.divModEquiv k).symm.summable_iff).mp hpair, ?_⟩
  have hineq := hpair.tsum_le_tsum hbound' hmajor
  rw [(Nat.divModEquiv k).symm.tsum_eq (fun l => f (l+1))] at hineq
  have hsum : (∑' x : ℕ × Fin k, C*ρ^x.1) = (k : ℝ)*C/(1-ρ) := by
    rw [hmajor.tsum_prod]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    simp_rw [← mul_assoc]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1, div_eq_mul_inv]
  exact hineq.trans_eq hsum

def primePowerMoment (p : ℕ) [Fact p.Prime] (k s l : ℕ) : ℝ :=
  primitiveCompleteMoment (p^l) k s

theorem primepower_ratio_le_quarter {p : ℕ} [Fact p.Prime]
    (k s : ℕ) (hks : k+2 ≤ s) :
    (p : ℝ)^k/(p : ℝ)^s ≤ 1/4 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  apply (primepower_ratio_le_inv_sq (p := p) k s hks).trans
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 4)
  nlinarith

/-- At a good prime, the entire positive-level Euler tail is `O(p⁻²)`
with an explicit constant independent of the prime. -/
theorem primePowerMoment_good_tail {p : ℕ} [Fact p.Prime]
    (k s : ℕ) (hk : 2 ≤ k) (hs : 6 ≤ s) (hks : k+2 ≤ s) (hpk : ¬ p ∣ k) :
    Summable (fun l => primePowerMoment p k s (l+1)) ∧
      (∑' l : ℕ, primePowerMoment p k s (l+1)) ≤ 16*(k : ℝ)^7/(p : ℝ)^2 := by
  have hr := primepower_ratio_le_quarter (p := p) k s hks
  have hh := summable_tail_of_block_bound (primePowerMoment p k s) k (by omega)
    (C := 8*(k : ℝ)^6/(p : ℝ)^2) (ρ := (p : ℝ)^k/(p : ℝ)^s)
    (by positivity) (by positivity) (by linarith)
    (fun l => primitiveCompleteMoment_nonneg (p^l) k s) (by
      intro u v
      exact primitiveCompleteMoment_good_blocks_le k s u (v.val+1) hk hs hks
        (by omega) (by omega) hpk)
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hden : (1/2 : ℝ) ≤ 1-(p : ℝ)^k/(p : ℝ)^s := by linarith
  have hnum : (0 : ℝ) ≤ (k : ℝ)*(8*(k : ℝ)^6/(p : ℝ)^2) := by positivity
  calc
    _ ≤ (k : ℝ)*(8*(k : ℝ)^6/(p : ℝ)^2)/(1/2) :=
      div_le_div_of_nonneg_left hnum (by norm_num) hden
    _ = _ := by ring

/-- An explicit finite local tail bound at every prime whenever the
actual block recursion is available. This handles exceptional primes. -/
theorem primePowerMoment_tail_of_recurrence {p : ℕ} [Fact p.Prime]
    (k s : ℕ) (hk : 1 ≤ k) (hks : k+2 ≤ s) (hrec : PrimePowerRecurrence p k) :
    Summable (fun l => primePowerMoment p k s (l+1)) ∧
      (∑' l : ℕ, primePowerMoment p k s (l+1)) ≤ 2*(k : ℝ)*(p : ℝ)^k := by
  have hr := primepower_ratio_le_quarter (p := p) k s hks
  have hh := summable_tail_of_block_bound (primePowerMoment p k s) k (by omega)
    (C := (p : ℝ)^k) (ρ := (p : ℝ)^k/(p : ℝ)^s)
    (by positivity) (by positivity) (by linarith)
    (fun l => primitiveCompleteMoment_nonneg (p^l) k s) (by
      intro u v
      exact primitiveCompleteMoment_blocks_trivial_le k s u (v.val+1) hk
        (by omega) (by omega) hrec)
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hden : (1/2 : ℝ) ≤ 1-(p : ℝ)^k/(p : ℝ)^s := by linarith
  calc
    _ ≤ (k : ℝ)*(p : ℝ)^k/(1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = _ := by ring

theorem degree8_primePowerMoment_summable {p : ℕ} [Fact p.Prime]
    (s : ℕ) (hs : 10 ≤ s) : Summable (primePowerMoment p 8 s) := by
  apply (summable_nat_add_iff 1).mp
  exact (primePowerMoment_tail_of_recurrence 8 s (by norm_num) (by omega)
    primePowerRecurrence_eight).1

theorem degree9_primePowerMoment_summable {p : ℕ} [Fact p.Prime]
    (s : ℕ) (hs : 11 ≤ s) : Summable (primePowerMoment p 9 s) := by
  apply (summable_nat_add_iff 1).mp
  exact (primePowerMoment_tail_of_recurrence 9 s (by norm_num) (by omega)
    primePowerRecurrence_nine).1

#print axioms primePowerMoment_good_tail
#print axioms degree8_primePowerMoment_summable
#print axioms degree9_primePowerMoment_summable

end Waring.EndgameCompletion
