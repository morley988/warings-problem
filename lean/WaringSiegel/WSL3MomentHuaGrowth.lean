import WaringSiegel.WSL3MomentHuaReduction
import WaringSiegel.WSL2MomentHuaCubic

/-!
# Uniform number-field bounds for all Hua induction fibers

The number of summands in each target is explicit.  Nonzero targets have
polynomial norm growth, so the proved ideal-divisor and unit bounds give
an arbitrary epsilon loss, uniformly in every finite archimedean box.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NumberField Classical

namespace WaringSiegel.WSL3
open WSL2
variable {K : Type*} [Field K] [NumberField K]

theorem place_sum_power_le (S : Finset (𝓞 K)) {P : ℝ} (hP : 0 ≤ P)
    (hS : ∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P)
    (k s : ℕ) (x : Fin s → S) (v : NumberField.InfinitePlace K) :
    v (((∑ i, (x i : 𝓞 K)^k : 𝓞 K) : K)) ≤ (s : ℝ) * P^k := by
  simp only [map_sum, map_pow]
  calc
    v (∑ i, ((x i : 𝓞 K) : K)^k) ≤ ∑ i, v (((x i : 𝓞 K) : K)^k) :=
      v.val.sum_le Finset.univ _
    _ ≤ ∑ _i : Fin s, P^k := by
      apply Finset.sum_le_sum
      intro i hi
      rw [map_pow]
      exact pow_le_pow_left₀ (apply_nonneg v _) (hS _ (x i).property v) k
    _ = _ := by simp

theorem tuplePowerDifference_norm_le (S : Finset (𝓞 K)) {P : ℝ} (hP : 0 ≤ P)
    (hS : ∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P)
    (k s : ℕ) (xy : (Fin s → S) × (Fin s → S)) :
    absNorm (tuplePowerDifference k s S xy) ≤
      (2 * (s : ℝ)) ^ Module.finrank ℚ K * P ^ (k * Module.finrank ℚ K) := by
  have hbox (v : NumberField.InfinitePlace K) :
      v ((tuplePowerDifference k s S xy : 𝓞 K) : K) ≤ 2 * (s : ℝ) * P^k := by
    have h := place_sub_le_twice
      (place_sum_power_le S hP hS k s xy.1) (place_sum_power_le S hP hS k s xy.2) v
    simpa only [tuplePowerDifference, mul_assoc] using h
  have h := absNorm_le_box (by positivity) hbox
  simpa only [mul_pow, ← pow_mul] using h

theorem tuplePowerDifference_divisors_rpow_bound (k s : ℕ) (hs : 0 < s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ S : Finset (𝓞 K),
      (∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P) →
      ∀ xy : (Fin s → S) × (Fin s → S), tuplePowerDifference k s S xy ≠ 0 →
      (((additiveDifferences S).filter (fun h => h ≠ 0 ∧ h ∣ tuplePowerDifference k s S xy)).card : ℝ) ≤
        C * P ^ ε := by
  obtain ⟨C, hC, hbound⟩ := ring_divisor_polynomial_norm_rpow_bound
    (K := K) (k * Module.finrank ℚ K) ((2 * (s : ℝ))^Module.finrank ℚ K) (by positivity) hε
  refine ⟨C, hC, ?_⟩
  intro P hP S hS xy ha
  apply hbound P hP (tuplePowerDifference k s S xy) ha
    (tuplePowerDifference_norm_le S (by linarith) hS k s xy)
  · intro h hh
    exact (Finset.mem_filter.mp hh).2.2
  · intro h hh v
    exact additiveDifferences_place_bound S hS (Finset.mem_filter.mp hh).1 v

/-- A reusable bound for the nonzero fibers in the J-th Hua step. -/
theorem numberField_hua_nonzero_fibers (k J : ℕ) (hJ : 1 ≤ J) (hJk : J < k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ P : ℝ, 1 ≤ P → ∀ S : Finset (𝓞 K),
      (∀ x ∈ S, ∀ v : NumberField.InfinitePlace K, v (x : K) ≤ P) →
      ∀ xy : (Fin (2^(J-1)) → S) × (Fin (2^(J-1)) → S),
        tuplePowerDifference k (2^(J-1)) S xy ≠ 0 →
      ((iteratedDifferenceFiber S (additiveDifferences S) k J
        (tuplePowerDifference k (2^(J-1)) S xy)).card : ℝ) ≤
        M * (P ^ Module.finrank ℚ K : ℝ)^ε := by
  let d := Module.finrank ℚ K
  have hd : (0 : ℝ) < d := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  have hJR : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  let η : ℝ := (d : ℝ) * ε / J
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨B, hB, hdiv⟩ := tuplePowerDifference_divisors_rpow_bound
    (K := K) k (2^(J-1)) (by positivity) hη
  have hdiff : 0 < k-J := Nat.sub_pos_of_lt hJk
  refine ⟨(k-J : ℕ)*B^J, by positivity, ?_⟩
  intro P hP S hS xy hxy
  have hPpos : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hpow : (B * P^η)^J = B^J * (P^d : ℝ)^ε := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (P^η) J, ← Real.rpow_mul hPpos.le,
      ← Real.rpow_natCast P d, ← Real.rpow_mul hPpos.le]
    congr 1
    dsimp [η]
    field_simp
  calc
    _ ≤ (k-J : ℕ)*
        (((additiveDifferences S).filter (fun h => h ≠ 0 ∧ h ∣ tuplePowerDifference k (2^(J-1)) S xy)).card : ℝ)^J := by
      exact_mod_cast iteratedDifference_fiber_card_le_divisors S (additiveDifferences S) k J hJk hxy
    _ ≤ (k-J : ℕ)*(B*P^η)^J := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (hdiv P hP S hS xy hxy) J) (by positivity)
    _ = _ := by rw [hpow]; ring

#print axioms numberField_hua_nonzero_fibers

end WaringSiegel.WSL3
