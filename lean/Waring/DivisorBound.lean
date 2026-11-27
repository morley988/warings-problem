import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The divisor bound for every positive exponent

This is a proof for the actual finite set `Nat.divisors`. It uses its exact
prime-factorization product, treats large primes with `v+1 <= 2^v`, and absorbs
the finitely many small primes into a constant independent of the integer.
No divisor estimate is assumed as a hypothesis.
-/

noncomputable section
open scoped BigOperators

namespace Waring.DivisorBound

/-- An elementary uniform bound for the polynomial factor in one prime's
multiplicity. The constant is finite and independent of the multiplicity. -/
theorem multiplicity_le_geometric (b : ℝ) (hb : 1 < b) (v : ℕ) :
    (v : ℝ) + 1 ≤ (b / (b - 1)) * b ^ v := by
  have hd : 0 < b-1 := by linarith
  have hc : 1 ≤ b/(b-1) := (one_le_div hd).mpr (by linarith)
  have hcpos : 0 < b/(b-1) := lt_of_lt_of_le zero_lt_one hc
  induction v with
  | zero => simpa using hc
  | succ v ih =>
    have hp : 1 ≤ b^v := one_le_pow₀ hb.le
    have hinc : 1 ≤ (b/(b-1))*b^v*(b-1) := by
      calc
        (1 : ℝ) ≤ b := hb.le
        _ ≤ b*b^v := le_mul_of_one_le_right (by linarith) hp
        _ = (b/(b-1))*b^v*(b-1) := by field_simp
    simp only [Nat.cast_succ, pow_succ]
    nlinarith

/-- Beyond a finite threshold, every prime base to the given positive power
is at least two. The lemma does not need primality. -/
theorem exists_large_base_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ p : ℕ, M ≤ p → (2 : ℝ) ≤ (p : ℝ)^ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((2 : ℝ) ^ ε⁻¹)
  refine ⟨M, ?_⟩
  intro p hp
  calc
    (2 : ℝ) = ((2 : ℝ)^ε⁻¹)^ε := (Real.rpow_inv_rpow (by norm_num) hε.ne').symm
    _ ≤ (p : ℝ)^ε := Real.rpow_le_rpow (by positivity)
      (hM.le.trans (by exact_mod_cast hp)) hε.le

/-- The exact factorization product commutes with real exponentiation. -/
theorem prime_factorization_rpow (n : ℕ) (hn : n ≠ 0) (ε : ℝ) :
    (∏ p ∈ n.primeFactors, ((p : ℝ)^ε)^(n.factorization p)) = (n : ℝ)^ε := by
  have hfactor : (∏ p ∈ n.primeFactors, p^(n.factorization p)) = n := by
    simpa only [Nat.prod_factorization_eq_prod_primeFactors] using
      Nat.factorization_prod_pow_eq_self hn
  calc
    _ = ∏ p ∈ n.primeFactors, (((p^(n.factorization p) : ℕ) : ℝ)^ε) := by
      apply Finset.prod_congr rfl
      intro p _
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity),
        ← Real.rpow_mul_natCast (by positivity)]
      congr 1
      ring
    _ = (∏ p ∈ n.primeFactors, ((p^(n.factorization p) : ℕ) : ℝ))^ε :=
      Real.finset_prod_rpow _ _ (fun _ _ => by positivity) ε
    _ = (n : ℝ)^ε := by rw [← Nat.cast_prod, hfactor]

/-- The classical divisor bound, with a positive real constant depending only
on epsilon and valid for every positive natural integer. -/
theorem divisor_count_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C*(n : ℝ)^ε := by
  let b : ℝ := (2 : ℝ)^ε
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := b/(b-1)
  have hc1 : 1 ≤ c := (one_le_div (by dsimp [b]; linarith : (0 : ℝ) < b-1)).mpr (by linarith)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  obtain ⟨M, hM⟩ := exists_large_base_threshold hε
  refine ⟨c^M, by positivity, ?_⟩
  intro n hn
  have hlocal : ∀ p ∈ n.primeFactors,
      ((n.factorization p : ℕ) : ℝ)+1 ≤
        (if p < M then c else 1) * ((p : ℝ)^ε)^(n.factorization p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hbp : b ≤ (p : ℝ)^ε := Real.rpow_le_rpow (by norm_num) hp2 hε.le
    by_cases hsmall : p < M
    · rw [if_pos hsmall]
      exact (multiplicity_le_geometric b hb _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbp _) hc0.le)
    · rw [if_neg hsmall, one_mul]
      have hv : ((n.factorization p : ℕ) : ℝ)+1 ≤ (2 : ℝ)^(n.factorization p) := by
        exact_mod_cast (Nat.lt_two_pow_self (n := n.factorization p))
      exact hv.trans (pow_le_pow_left₀ (by norm_num) (hM p (Nat.le_of_not_gt hsmall)) _)
  have hconstant : (∏ p ∈ n.primeFactors, if p < M then c else 1) ≤ c^M := by
    rw [← Finset.prod_filter (fun p => p < M) (fun _ => c), Finset.prod_const]
    apply pow_le_pow_right₀ hc1
    have hsubset : n.primeFactors.filter (fun p => p < M) ⊆ Finset.range M := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsubset
  rw [Nat.card_divisors hn.ne', Nat.cast_prod]
  calc
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < M then c else 1) * ((p : ℝ)^ε)^(n.factorization p) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p hp
      simpa only [Nat.cast_add, Nat.cast_one] using hlocal p hp
    _ = (∏ p ∈ n.primeFactors, if p < M then c else 1) * (n : ℝ)^ε := by
      rw [Finset.prod_mul_distrib, prime_factorization_rpow n hn.ne']
    _ ≤ c^M*(n : ℝ)^ε := mul_le_mul_of_nonneg_right hconstant (by positivity)

/-- A single finite constant controls all divisors of all positive integers
up to a real cutoff. This form supplies the multiplicity parameter in counting
lemmas without a new divisor-bound hypothesis. -/
theorem divisor_count_le_cutoff_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X → ∀ n : ℕ, 0 < n → (n : ℝ) ≤ X →
      (n.divisors.card : ℝ) ≤ C*X^ε := by
  obtain ⟨C, hC, hbound⟩ := divisor_count_le_rpow hε
  refine ⟨C, hC, ?_⟩
  intro X _ n hn hnX
  exact (hbound n hn).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hnX hε.le) hC.le)

#print axioms divisor_count_le_rpow
#print axioms divisor_count_le_cutoff_rpow

end Waring.DivisorBound
