import Waring.EndgameCompletionHarmonic
import Waring.ProductMultiplicity

/-!
# Actual height-product divisor averaging on the auxiliary major arcs

A pointwise ratio comparison reduces the fractional weight directly to
the proved gcd-weighted harmonic sum. Product grouping then handles any
actual finite family of positive height tuples, with a uniform P^epsilon
loss. No mean value or divisor-average premise is introduced.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionMajorAverage
open EndgameCompletion ProductMultiplicity

theorem fractional_weight_le_harmonic {d n H A θ : ℝ}
    (hd : 1≤d) (hn : 0<n) (hnH : n≤H) (hA : 0≤A) (hθ : 0≤θ) (hθ1 : θ≤1) :
    d^θ*(1+A*n)^(-θ) ≤ (d*H/n)*(1+A*H)^(-θ) := by
  have hH : 0<H := hn.trans_le hnH
  have hd0 : 0<d := zero_lt_one.trans_le hd
  have hb : 0<1+A*n := by positivity
  have hbH : 0<1+A*H := by positivity
  have hratio : 1≤d*H/n := by
    apply (le_div_iff₀ hn).mpr
    nlinarith
  have hbase : d/(1+A*n) ≤ (d*H/n)/(1+A*H) := by
    apply (div_le_div_iff₀ hb hbH).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hn).mpr
    nlinarith
  calc
    _ = (d/(1+A*n))^θ := by rw [Real.div_rpow hd0.le hb.le, Real.rpow_neg hb.le]; rfl
    _ ≤ ((d*H/n)/(1+A*H))^θ := Real.rpow_le_rpow (by positivity) hbase hθ
    _ = (d*H/n)^θ*(1+A*H)^(-θ) := by
      rw [Real.div_rpow (by positivity) hbH.le, Real.rpow_neg hbH.le]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hratio hθ1)
      (Real.rpow_nonneg hbH.le _)

theorem gcd_weight_sum_le (q N : ℕ) (hq : 0<q) (hN : 0<N)
    {A θ : ℝ} (hA : 0≤A) (hθ : 0≤θ) (hθ1 : θ≤1) :
    (∑ n ∈ Finset.Icc 1 N,
      (Nat.gcd q n:ℝ)^θ*(1+A*(n:ℝ))^(-θ)) ≤
      (N:ℝ)*(1+A*(N:ℝ))^(-θ)*(q.divisors.card:ℝ)*(harmonic N:ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        ((Nat.gcd q n:ℝ)*(N:ℝ)/(n:ℝ))*(1+A*(N:ℝ))^(-θ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      apply fractional_weight_le_harmonic _ (by exact_mod_cast hn'.1) (by exact_mod_cast hn'.2) hA hθ hθ1
      exact_mod_cast Nat.gcd_pos_of_pos_left n hq
    _ = ((N:ℝ)*(1+A*(N:ℝ))^(-θ))*
        ∑ n ∈ Finset.Icc 1 N, (Nat.gcd n q:ℝ)/(n:ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [Nat.gcd_comm q n]
      ring
    _ ≤ ((N:ℝ)*(1+A*(N:ℝ))^(-θ))*((q.divisors.card:ℝ)*(harmonic N:ℝ)) :=
      mul_le_mul_of_nonneg_left (gcd_harmonic_sum_le q N hq) (by positivity)
    _ = _ := by ring

theorem height_product_major_average (r : ℕ) {B ε : ℝ} (hB : 0≤B) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (P : ℝ), 1≤P → ∀ (q N : ℕ), 0<q → 0<N →
      (q:ℝ)≤P^B → (N:ℝ)≤P^B → ∀ (S : Finset (Fin r → ℕ)) (A θ : ℝ),
      (∀ x ∈ S, tupleProduct x ∈ Finset.Icc 1 N) → 0≤A → 0≤θ → θ≤1 →
      (∑ x ∈ S, (Nat.gcd q (tupleProduct x):ℝ)^θ*
        (1+A*(tupleProduct x:ℝ))^(-θ)) ≤
      C*P^ε*(N:ℝ)*(1+A*(N:ℝ))^(-θ) := by
  let δ : ℝ := ε/(3*(B+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hthird : 0<ε/3 := by positivity
  have hBδ : B*δ≤ε/3 := by
    have hid : δ*(3*(B+1))=ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  obtain ⟨Cg,hCg,hgroup⟩ := weighted_product_grouping_polynomial r hB hthird
  obtain ⟨Cd,hCd,hdiv⟩ := DivisorBound.divisor_count_le_rpow hδ
  let Ch : ℝ := 1+1/δ
  have hCh : 0<Ch := by dsimp [Ch]; positivity
  refine ⟨Cg*Cd*Ch, by positivity, ?_⟩
  intro P hP q N hq hN hqP hNP S A θ hmap hA hθ hθ1
  have hPpos : 0<P := zero_lt_one.trans_le hP
  have hpower (n : ℕ) (hnP : (n:ℝ)≤P^B) : (n:ℝ)^δ≤P^(ε/3) := by
    calc
      _ ≤ (P^B)^δ := Real.rpow_le_rpow (Nat.cast_nonneg _) hnP hδ.le
      _ = P^(B*δ) := (Real.rpow_mul hPpos.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hBδ
  have hdq : (q.divisors.card:ℝ)≤Cd*P^(ε/3) :=
    (hdiv q hq).trans (mul_le_mul_of_nonneg_left (hpower q hqP) hCd.le)
  have hhN : (harmonic N:ℝ)≤Ch*P^(ε/3) :=
    (harmonic_le_rpow N hN hδ).trans (mul_le_mul_of_nonneg_left (hpower N hNP) hCh.le)
  have hhar0 : 0≤(harmonic N:ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hweights := mul_le_mul hdq hhN hhar0 (by positivity)
  have hsum := gcd_weight_sum_le q N hq hN hA hθ hθ1
  have hgrouped := hgroup P hP N hN hNP S
    (fun n => (Nat.gcd q n:ℝ)^θ*(1+A*(n:ℝ))^(-θ)) hmap (fun _ _ => by positivity)
  apply hgrouped.trans
  calc
    _ ≤ Cg*P^(ε/3)*((N:ℝ)*(1+A*(N:ℝ))^(-θ)*(q.divisors.card:ℝ)*(harmonic N:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (Cg*P^(ε/3)*((N:ℝ)*(1+A*(N:ℝ))^(-θ)))*
        ((q.divisors.card:ℝ)*(harmonic N:ℝ)) := by ring
    _ ≤ (Cg*P^(ε/3)*((N:ℝ)*(1+A*(N:ℝ))^(-θ)))*
        ((Cd*P^(ε/3))*(Ch*P^(ε/3))) :=
      mul_le_mul_of_nonneg_left hweights (by positivity)
    _ = _ := by
      have hp : P^ε=P^(ε/3)*P^(ε/3)*P^(ε/3) := by
        rw [← Real.rpow_add hPpos, ← Real.rpow_add hPpos]
        congr 1
        ring
      rw [hp]
      dsimp [Ch]
      ring

#print axioms gcd_weight_sum_le
#print axioms height_product_major_average
end Waring.PolicyCompletionMajorAverage
