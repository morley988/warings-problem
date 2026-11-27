import Waring.EndgameCompletionEulerLocal
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries

/-!
# Absolute convergence of ordinary major-arc arithmetic coefficients

The zero-extended primitive coefficients are multiplicative. Positive
local tails are summably small away from the exceptional prime, whose
entire local series has already been proved finite.
-/

noncomputable section

open scoped BigOperators

namespace Waring.EndgameCompletion

def completeCoefficient (k s q : ℕ) : ℝ :=
  if hq : q=0 then 0 else
    letI : NeZero q := ⟨hq⟩
    primitiveCompleteMoment q k s

@[simp] theorem completeCoefficient_zero (k s : ℕ) : completeCoefficient k s 0=0 := by
  simp [completeCoefficient]

theorem completeCoefficient_nezero (q k s : ℕ) [NeZero q] :
    completeCoefficient k s q=primitiveCompleteMoment q k s := by
  rw [completeCoefficient, dif_neg (NeZero.ne q)]

theorem completeCoefficient_nonneg (k s q : ℕ) : 0 ≤ completeCoefficient k s q := by
  by_cases hq : q=0
  · simp [hq]
  · letI : NeZero q := ⟨hq⟩
    rw [completeCoefficient_nezero]
    exact primitiveCompleteMoment_nonneg q k s

theorem completeMonomialSumMod_one (k : ℕ) (a : ZMod 1) :
    completeMonomialSumMod 1 k a=1 := by
  unfold completeMonomialSumMod
  have hh (x : ZMod 1) : a*x^k=0 := Subsingleton.elim _ _
  simp [hh, AddChar.map_zero_eq_one]

@[simp] theorem completeCoefficient_one (k s : ℕ) : completeCoefficient k s 1=1 := by
  rw [completeCoefficient_nezero]
  letI : Unique (ZMod 1)ˣ := uniqueOfSubsingleton 1
  simp [primitiveCompleteMoment, normalizedCompleteSum, completeMonomialSumMod_one]

theorem completeCoefficient_coprime (k s : ℕ) (hk : 0 < k)
    {q r : ℕ} (hqr : q.Coprime r) :
    completeCoefficient k s (q*r)=completeCoefficient k s q*completeCoefficient k s r := by
  by_cases hq : q=0
  · simp [hq]
  by_cases hr : r=0
  · simp [hr]
  letI : NeZero q := ⟨hq⟩
  letI : NeZero r := ⟨hr⟩
  rw [completeCoefficient_nezero, completeCoefficient_nezero, completeCoefficient_nezero]
  exact primitiveCompleteMoment_coprime q r k s hqr hk

theorem completeCoefficient_primepower {p : ℕ} [Fact p.Prime] (k s l : ℕ) :
    completeCoefficient k s (p^l)=primePowerMoment p k s l :=
  completeCoefficient_nezero (p^l) k s

/-- A nonnegative multiplicative function is summable if all local
series converge and their excesses over one have a summable majorant.
The proof bounds finite smooth-number sums by an exponential product. -/
theorem summable_multiplicative_of_local_bound (f b : ℕ → ℝ)
    (hf0 : f 0=0) (hf1 : f 1=1)
    (hmul : ∀ {m n}, m.Coprime n → f (m*n)=f m*f n)
    (hf : ∀ n, 0 ≤ f n) (hb : ∀ n, 0 ≤ b n) (hbsum : Summable b)
    (hlocal : ∀ p, p.Prime → Summable (fun l : ℕ => f (p^l)))
    (hbound : ∀ p, p.Prime → (∑' l : ℕ, f (p^l)) ≤ 1+b p) : Summable f := by
  apply summable_of_sum_range_le hf (c := Real.exp (∑' p : ℕ, b p))
  intro N
  have hsmooth := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 (fun {m n} h => hmul h) (fun {p} hp => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using hlocal p hp) N
  have hind : Summable ((Nat.smoothNumbers N).indicator f) :=
    summable_subtype_iff_indicator.mp hsmooth.2.summable
  calc
    _ ≤ ∑ n ∈ Finset.range N, (Nat.smoothNumbers N).indicator f n := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n=0
      · rw [hn0, hf0]
        exact Set.indicator_nonneg (fun x _ => hf x) 0
      · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt
          (Nat.pos_of_ne_zero hn0) (Finset.mem_range.mp hn))]
    _ ≤ ∑' n : ℕ, (Nat.smoothNumbers N).indicator f n :=
      hind.sum_le_tsum _ (fun n _ => Set.indicator_nonneg (fun x _ => hf x) n)
    _ = ∏ p ∈ N.primesBelow, ∑' l : ℕ, f (p^l) := by
      rw [← tsum_subtype]
      exact hsmooth.2.tsum_eq
    _ ≤ ∏ p ∈ N.primesBelow, Real.exp (b p) := by
      apply Finset.prod_le_prod (fun p _ => tsum_nonneg (fun _ => hf _))
      intro p hp
      exact (hbound p (Nat.prime_of_mem_primesBelow hp)).trans (by
        simpa only [add_comm] using Real.add_one_le_exp (b p))
    _ = Real.exp (∑ p ∈ N.primesBelow, b p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' p : ℕ, b p) :=
      Real.exp_le_exp.mpr (hbsum.sum_le_tsum _ (fun n _ => hb n))

theorem primePowerMoment_zero {p : ℕ} [Fact p.Prime] (k s : ℕ) :
    primePowerMoment p k s 0=1 := by
  rw [← completeCoefficient_primepower, pow_zero, completeCoefficient_one]

/-- The complete coefficient series is summable once the exact
prime-power recurrence is available at every prime. -/
theorem completeCoefficient_summable_of_recurrence (k s : ℕ)
    (hk : 2 ≤ k) (hs : 6 ≤ s) (hks : k+2 ≤ s)
    (hrec : ∀ (p : ℕ) (hp : p.Prime), @PrimePowerRecurrence p k ⟨hp⟩) :
    Summable (completeCoefficient k s) := by
  let D : ℝ := 16*(k : ℝ)^7
  let E : ℝ := 2*(k : ℝ)*(k : ℝ)^k
  let b : ℕ → ℝ := fun n => D/(n : ℝ)^2 + if n ≤ k then E else 0
  have hb (n : ℕ) : 0 ≤ b n := by
    dsimp [b, D, E]
    split_ifs <;> positivity
  have hbsum : Summable b := by
    have hpseries : Summable (fun n : ℕ => D/(n : ℝ)^2) := by
      simpa only [mul_one_div] using
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).mul_left D
    have hfinite : Summable (fun n : ℕ => if n ≤ k then E else 0) := by
      apply summable_of_ne_finset_zero (s := Finset.range (k+1))
      intro n hn
      rw [if_neg]
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    exact hpseries.add hfinite
  have hlocal (p : ℕ) (hp : p.Prime) :
      Summable (fun l : ℕ => completeCoefficient k s (p^l)) := by
    letI : Fact p.Prime := ⟨hp⟩
    have hh := (primePowerMoment_tail_of_recurrence k s (by omega) hks (hrec p hp)).1
    have hall : Summable (primePowerMoment p k s) := (summable_nat_add_iff 1).mp hh
    simpa only [completeCoefficient_primepower] using hall
  apply summable_multiplicative_of_local_bound (completeCoefficient k s) b
    (completeCoefficient_zero k s) (completeCoefficient_one k s)
    (completeCoefficient_coprime k s (by omega)) (completeCoefficient_nonneg k s) hb hbsum hlocal
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  have htail := primePowerMoment_tail_of_recurrence k s (by omega) hks (hrec p hp)
  have hsum : (∑' l : ℕ, completeCoefficient k s (p^l)) =
      1+∑' l : ℕ, primePowerMoment p k s (l+1) := by
    simp only [completeCoefficient_primepower]
    have heq := htail.1.sum_add_tsum_nat_add' (f := primePowerMoment p k s)
    simpa only [Finset.sum_range_one, primePowerMoment_zero] using heq.symm
  rw [hsum]
  apply add_le_add_left
  by_cases hpk : p ≤ k
  · have hpow : (p : ℝ)^k ≤ (k : ℝ)^k :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hpk) k
    have hlarge : 2*(k : ℝ)*(p : ℝ)^k ≤ E :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    dsimp [b]
    rw [if_pos hpk]
    exact htail.2.trans (hlarge.trans (le_add_of_nonneg_left (by dsimp [D]; positivity)))
  · have hndiv : ¬ p ∣ k := fun hd => hpk (Nat.le_of_dvd (by omega) hd)
    have hgood := (primePowerMoment_good_tail k s hk hs hks hndiv).2
    simpa only [b, if_neg hpk, add_zero, D] using hgood

/-- Absolute arithmetic convergence at the full degree-eight major-arc
threshold, including the exceptional prime two. -/
theorem degree8_completeCoefficient_summable (s : ℕ) (hs : 10 ≤ s) :
    Summable (completeCoefficient 8 s) := by
  apply completeCoefficient_summable_of_recurrence 8 s (by norm_num) (by omega) (by omega)
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact primePowerRecurrence_eight

/-- Absolute arithmetic convergence at the full degree-nine major-arc
threshold, including the exceptional prime three. -/
theorem degree9_completeCoefficient_summable (s : ℕ) (hs : 11 ≤ s) :
    Summable (completeCoefficient 9 s) := by
  apply completeCoefficient_summable_of_recurrence 9 s (by norm_num) (by omega) (by omega)
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact primePowerRecurrence_nine

#print axioms summable_multiplicative_of_local_bound
#print axioms degree8_completeCoefficient_summable
#print axioms degree9_completeCoefficient_summable

end Waring.EndgameCompletion
