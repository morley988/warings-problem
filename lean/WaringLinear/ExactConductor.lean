import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! # Exact-conductor inversion for the small Gram blocks -/
noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction
namespace WaringLinear

/-- A divisor projector can be inverted before taking its operator norm.
The factor depends on the divisor count of the fixed ambient modulus. -/
theorem conductor_cutoff_sum {ι : Type*} [Fintype ι] (r : ι→ℕ) (A : ι→ℂ)
    (Q M : ℕ) (C : ℝ) (hQ : Q≠0) (hC : 0≤C) (hr : ∀i,r i∣Q)
    (hblock : ∀ d∈Q.divisors,d≤M → ‖∑i∈Finset.univ.filter (fun i => r i∣d),A i‖≤C) :
    ‖∑i∈Finset.univ.filter (fun i => r i≤M),A i‖ ≤ (Q.divisors.card:ℝ)^2*C := by
  classical
  let F (d:ℕ) := ∑i∈Finset.univ.filter (fun i => r i=d),A i
  let G (d:ℕ) := ∑i∈Finset.univ.filter (fun i => r i∣d),A i
  have hh (d:ℕ) (hd:0<d) : ∑e∈d.divisors,F e=G d := by
    simp only [F,G,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp [Nat.mem_divisors,hd.ne',eq_comm]
  have hInv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hh
  have hm (e) (he:e∈Q.divisors) (hc:e≤M) : ‖F e‖≤(Q.divisors.card:ℝ)*C := by
    have ed := (Nat.mem_divisors.mp he).1
    have h := hInv e (Nat.pos_of_mem_divisors he)
    rw [Nat.sum_divisorsAntidiagonal' (f:=fun a b => (ArithmeticFunction.moebius a:ℂ)*G b)] at h
    rw [←h]
    calc
      _ ≤ ∑d∈e.divisors,‖(ArithmeticFunction.moebius (e/d):ℂ)*G d‖ := norm_sum_le _ _
      _ ≤ ∑ _d∈e.divisors,C := by
        apply Finset.sum_le_sum
        intro d hd
        have dd := (Nat.mem_divisors.mp hd).1
        have hmu : ‖(ArithmeticFunction.moebius (e/d):ℂ)‖≤1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n:=e/d))
        have hG := hblock d (Nat.mem_divisors.mpr ⟨dd.trans ed,hQ⟩) ((Nat.le_of_dvd (Nat.pos_of_mem_divisors he) dd).trans hc)
        rw [norm_mul]
        exact (mul_le_mul hmu hG (norm_nonneg _) zero_le_one).trans (by simp)
      _ ≤ _ := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ hC
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hQ ed)
  let D := Q.divisors.filter (·≤M)
  have H : (∑e∈D,F e)=∑i∈Finset.univ.filter (fun i => r i≤M),A i := by
    simp only [F,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp [D,eq_comm,Nat.mem_divisors,hr i,hQ]
  rw [←H]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _e∈D,(Q.divisors.card:ℝ)*C :=
      Finset.sum_le_sum (fun e he => hm _ (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2)
    _ ≤ (Q.divisors.card:ℝ)*((Q.divisors.card:ℝ)*C) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hC)
      exact_mod_cast Finset.card_filter_le (s:=Q.divisors) (·≤M)
    _ = _ := by ring

/-- The divisor loss is bounded independently of the locations of the
prime windows when each mark is used once. -/
theorem squarefree_power_divisor_count (m k : ℕ) (hm : Squarefree m) :
    (m^k).divisors.card ≤ (k+1)^m.primeFactors.card := by
  classical
  rcases eq_or_ne k 0 with rfl|hk
  · simp
  have hm0 : m≠0 := hm.ne_zero
  rw [Nat.card_divisors (pow_ne_zero k hm0),Nat.primeFactors_pow m hk]
  calc
    _ ≤ ∏ _p∈m.primeFactors,(k+1) := by
      apply Finset.prod_le_prod'
      intro p _
      rw [Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_left k (hm.natFactorization_le_one p)).trans (by simp)) _
    _ = _ := by simp

#print axioms conductor_cutoff_sum
#print axioms squarefree_power_divisor_count
end WaringLinear
