import Waring.PolicyCompletionMajorFamily
import Waring.SeedCompletionPhaseSize

/-! # Uniform parity, monotonicity, and divisor labels of every terminal phase -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionTerminalPhase
open Polynomial IntegerDifferencePolynomial PolicyCompletionPositivePhase
open PolicyCompletionPhaseContent PolicyCompletionMajorFamily

theorem powerPolynomial_parity (k : ℕ) (params : List (ℤ × ℤ))
    (hm : ∀ p ∈ params, p.2 ≠ 0) (z : ℝ) :
    (powerPolynomial k params).eval₂ (Int.castRingHom ℝ) (-z) =
      (-1 : ℝ)^(k+params.length)*(powerPolynomial k params).eval₂ (Int.castRingHom ℝ) z := by
  induction params generalizing z with
  | nil =>
    simp only [powerPolynomial,List.length_nil,Nat.add_zero,Polynomial.eval₂_pow,Polynomial.eval₂_X]
    exact neg_pow z k
  | cons p rest ih =>
    have hp : p.2 ≠ 0 := hm p (List.mem_cons_self ..)
    have hr : ∀ q ∈ rest, q.2 ≠ 0 := fun q hq => hm q (List.mem_cons_of_mem _ hq)
    simp only [powerPolynomial,List.length_cons]
    rw [difference_eval_real k p.1 p.2 _ hp,difference_eval_real k p.1 p.2 _ hp]
    rw [show -z+(p.1 : ℝ)*(p.2 : ℝ)^k = -(z-(p.1 : ℝ)*(p.2 : ℝ)^k) by ring,
      show -z-(p.1 : ℝ)*(p.2 : ℝ)^k = -(z+(p.1 : ℝ)*(p.2 : ℝ)^k) by ring,
      ih hr,ih hr,Nat.add_succ,pow_succ]
    ring

def phase {j : ℕ} (k : ℕ) (h m : Fin j → ℕ) (z : ℕ) : ℤ :=
  (powerPolynomial k (naturalParameters h m)).eval (z : ℤ)

def realPolynomial {j : ℕ} (k : ℕ) (h m : Fin j → ℕ) : Polynomial ℝ :=
  (powerPolynomial k (naturalParameters h m)).map (Int.castRingHom ℝ)

theorem realPolynomial_eval {j : ℕ} (k : ℕ) (h m : Fin j → ℕ) (z : ℕ) :
    (realPolynomial k h m).eval (z : ℝ)=(phase k h m z : ℝ) := by
  simp [realPolynomial,phase,Polynomial.eval_natCast_map]

theorem realPolynomial_parity {j : ℕ} (k : ℕ) (h m : Fin j → ℕ)
    (hm : ∀ i, 0 < m i) (z : ℝ) :
    (realPolynomial k h m).eval (-z)=(-1 : ℝ)^(k+j)*(realPolynomial k h m).eval z := by
  have H := powerPolynomial_parity k (naturalParameters h m) (by
    simp only [naturalParameters,List.forall_mem_ofFn_iff]
    intro i
    exact_mod_cast (hm i).ne') z
  simpa only [realPolynomial,Polynomial.eval_map,naturalParameters_length] using H

theorem parity_square (k j : ℕ) : ((-1 : ℝ)^(k+j))^2=1 := by
  rw [← pow_mul,Nat.mul_comm, pow_mul]
  norm_num

theorem phase_strictMono {j : ℕ} {k : ℕ} (hj : j < k) (h m : Fin j → ℕ)
    (hh : ∀ i, 0 < h i) (hm : ∀ i, 0 < m i) : StrictMono (phase k h m) := by
  have H := powerPolynomial_eval_strictMonoOn k (naturalParameters h m)
    (naturalParameters_pos h m hh hm) (by simpa using hj)
  intro x y hxy
  exact H (Int.natCast_nonneg x) (Int.natCast_nonneg y) (by exact_mod_cast hxy)

theorem phase_pos {j : ℕ} {k : ℕ} (hj : j < k) (h m : Fin j → ℕ)
    (hh : ∀ i, 0 < h i) (hm : ∀ i, 0 < m i) {z : ℕ} (hz : 0 < z) :
    0 < phase k h m z := by
  have hn : 0 ≤ phase k h m 0 := by
    simp only [phase,Nat.cast_zero,← Polynomial.coeff_zero_eq_eval_zero]
    exact powerPolynomial_coeff_nonneg k (naturalParameters h m)
      (fun p hp => ⟨(naturalParameters_pos h m hh hm p hp).1.le,
        (naturalParameters_pos h m hh hm p hp).2⟩) 0
  exact hn.trans_lt (phase_strictMono hj h m hh hm hz)

theorem realPolynomial_natDegree {j : ℕ} {k : ℕ} (hj : j ≤ k) (h m : Fin j → ℕ)
    (hh : ∀ i, 0 < h i) (hm : ∀ i, 0 < m i) :
    (realPolynomial k h m).natDegree=k-j := by
  rw [realPolynomial,Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℝ)),
    powerPolynomial_natDegree]
  · simp
  · exact fun p hp => ⟨(naturalParameters_pos h m hh hm p hp).1.ne',
      (naturalParameters_pos h m hh hm p hp).2.ne'⟩
  · simpa using hj

theorem realPolynomial_leadingCoeff {j : ℕ} {k : ℕ} (hj : j ≤ k) (h m : Fin j → ℕ)
    (hh : ∀ i, 0 < h i) (hm : ∀ i, 0 < m i) :
    (realPolynomial k h m).leadingCoeff =
      (leadingMultiplier k j : ℝ) * ∏ i, (h i : ℝ) := by
  rw [realPolynomial,Polynomial.leadingCoeff_map' (Int.cast_injective (α := ℝ)),
    powerPolynomial_leadingCoeff]
  · simp [naturalParameters_heightProduct,ProductMultiplicity.tupleProduct]
  · exact fun p hp => ⟨(naturalParameters_pos h m hh hm p hp).1.ne',
      (naturalParameters_pos h m hh hm p hp).2.ne'⟩
  · simpa using hj

theorem height_dvd_phase {j : ℕ} (k : ℕ) (h m : Fin j → ℕ)
    (hm : ∀ i, 0 < m i) (z : ℕ) (i : Fin j) : (h i : ℤ) ∣ phase k h m z := by
  obtain ⟨g,hg⟩ := powerPolynomial_height_factor k (naturalParameters h m) (by
    simp only [naturalParameters,List.forall_mem_ofFn_iff]
    intro r
    exact_mod_cast (hm r).ne')
  have hd : (h i : ℤ) ∣ heightProduct (naturalParameters h m) := by
    simp only [heightProduct,naturalParameters,List.map_ofFn,Function.comp_def,List.prod_ofFn]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  unfold phase
  rw [hg,Polynomial.eval_mul,Polynomial.eval_C]
  exact dvd_mul_of_dvd_left hd _

#print axioms powerPolynomial_parity
#print axioms phase_pos
#print axioms height_dvd_phase
end Waring.SeedCompletionTerminalPhase
