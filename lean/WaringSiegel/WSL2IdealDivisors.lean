import WaringSiegel.WSL2IdealNorm
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# WSL2: an epsilon bound for the number of ideal divisors

The elementary small-prime/large-prime argument in the classical Waring
project is extended to the actual unique factorization of integral ideals.
Finitely many ideals of bounded absolute norm replace finitely many small
rational primes. No ideal-divisor estimate is assumed.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open UniqueFactorizationMonoid

namespace WaringSiegel.IdealDivisorBounds
variable {K : Type*} [Field K] [NumberField K]

theorem multiplicity_le_geometric (b : ℝ) (hb : 1 < b) (v : ℕ) :
    (v : ℝ) + 1 ≤ (b / (b - 1)) * b ^ v := by
  have hd : 0 < b - 1 := by linarith
  have hc : 1 ≤ b / (b - 1) := (one_le_div hd).mpr (by linarith)
  induction v with
  | zero => simpa using hc
  | succ v ih =>
    have hp : 1 ≤ b ^ v := one_le_pow₀ hb.le
    have hinc : 1 ≤ (b / (b - 1)) * b ^ v * (b - 1) := by
      calc
        (1 : ℝ) ≤ b := hb.le
        _ ≤ b * b ^ v := le_mul_of_one_le_right (by linarith) hp
        _ = (b / (b - 1)) * b ^ v * (b - 1) := by field_simp
    simp only [Nat.cast_succ, pow_succ]
    nlinarith

theorem exists_large_base_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ q : ℕ, M ≤ q → (2 : ℝ) ≤ (q : ℝ) ^ ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((2 : ℝ) ^ ε⁻¹)
  refine ⟨M, ?_⟩
  intro q hq
  calc
    (2 : ℝ) = ((2 : ℝ) ^ ε⁻¹) ^ ε :=
      (Real.rpow_inv_rpow (by norm_num) hε.ne').symm
    _ ≤ (q : ℝ) ^ ε := Real.rpow_le_rpow (by positivity)
      (hM.le.trans (by exact_mod_cast hq)) hε.le

theorem ideal_factor_norm_ge_two (A P : Ideal (𝓞 K))
    (hP : P ∈ normalizedFactors A) : 2 ≤ Ideal.absNorm P := by
  have hp := irreducible_of_normalized_factor P hP
  have hn0 : Ideal.absNorm P ≠ 0 := mt Ideal.absNorm_eq_zero_iff.mp hp.ne_zero
  have hn1 : Ideal.absNorm P ≠ 1 := by
    intro hn
    have htop := Ideal.absNorm_eq_one_iff.mp hn
    exact hp.not_isUnit (by
      rw [htop]
      simpa only [Ideal.one_eq_top] using (isUnit_one : IsUnit (1 : Ideal (𝓞 K))))
  omega

/-- The divisor factor counts determine an ideal uniquely, and each factor
count ranges from zero to the corresponding count of the target ideal. -/
theorem ideal_divisor_card_le_product (A : Ideal (𝓞 K)) (hA : A ≠ 0)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ J ∈ S, J ∣ A) :
    S.card ≤ ∏ P ∈ (normalizedFactors A).toFinset,
      ((normalizedFactors A).count P + 1) := by
  classical
  let F := (normalizedFactors A).toFinset
  have hnonzero : ∀ J ∈ S, J ≠ 0 := by
    intro J hJ hz
    have h := hS J hJ
    rw [hz, zero_dvd_iff] at h
    exact hA h
  have hfactor : ∀ J ∈ S, normalizedFactors J ≤ normalizedFactors A := by
    intro J hJ
    exact (dvd_iff_normalizedFactors_le_normalizedFactors (hnonzero J hJ) hA).mp (hS J hJ)
  let enc : S → ∀ P : F, Fin ((normalizedFactors A).count (P : Ideal (𝓞 K)) + 1) :=
    fun J P => ⟨(normalizedFactors (J : Ideal (𝓞 K))).count (P : Ideal (𝓞 K)),
      Nat.lt_succ_of_le (Multiset.count_le_of_le (P : Ideal (𝓞 K)) (hfactor J J.property))⟩
  have henc : Function.Injective enc := by
    intro J L h
    apply Subtype.ext
    apply associated_iff_eq.mp
    apply (associated_iff_normalizedFactors_eq_normalizedFactors
      (hnonzero J J.property) (hnonzero L L.property)).mpr
    apply Multiset.ext.mpr
    intro P
    by_cases hP : P ∈ F
    · exact congrArg Fin.val (congrFun h ⟨P, hP⟩)
    · have hnot : P ∉ normalizedFactors A := by simpa only [F, Multiset.mem_toFinset] using hP
      have hJ : P ∉ normalizedFactors (J : Ideal (𝓞 K)) :=
        fun hmem => hnot (Multiset.mem_of_le (hfactor J J.property) hmem)
      have hL : P ∉ normalizedFactors (L : Ideal (𝓞 K)) :=
        fun hmem => hnot (Multiset.mem_of_le (hfactor L L.property) hmem)
      simp only [Multiset.count_eq_zero_of_notMem hJ, Multiset.count_eq_zero_of_notMem hL]
  have hcard := Fintype.card_le_of_injective enc henc
  simp only [Fintype.card_coe, Fintype.card_pi, Fintype.card_fin] at hcard
  convert hcard using 1
  exact (Finset.prod_coe_sort F (fun P => (normalizedFactors A).count P + 1)).symm

theorem ideal_factor_norm_product (A : Ideal (𝓞 K)) (hA : A ≠ 0) :
    (∏ P ∈ (normalizedFactors A).toFinset,
      (Ideal.absNorm P) ^ (normalizedFactors A).count P) = Ideal.absNorm A := by
  rw [← Finset.prod_multiset_map_count]
  rw [← map_multiset_prod, prod_normalizedFactors_eq_self hA]

theorem ideal_factor_norm_rpow (A : Ideal (𝓞 K)) (hA : A ≠ 0) (ε : ℝ) :
    (∏ P ∈ (normalizedFactors A).toFinset,
      ((Ideal.absNorm P : ℝ) ^ ε) ^ (normalizedFactors A).count P) =
      (Ideal.absNorm A : ℝ) ^ ε := by
  calc
    _ = ∏ P ∈ (normalizedFactors A).toFinset,
        (((Ideal.absNorm P) ^ (normalizedFactors A).count P : ℕ) : ℝ) ^ ε := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (by positivity),
        ← Real.rpow_mul_natCast (by positivity)]
      congr 1
      ring
    _ = (∏ P ∈ (normalizedFactors A).toFinset,
        (((Ideal.absNorm P) ^ (normalizedFactors A).count P : ℕ) : ℝ)) ^ ε :=
      Real.finset_prod_rpow _ _ (fun _ _ => by positivity) ε
    _ = (Ideal.absNorm A : ℝ) ^ ε := by
      rw [← Nat.cast_prod, ideal_factor_norm_product A hA]

/-- The multiplicative divisor product has epsilon growth in the actual
absolute norm, with a constant independent of the ideal. -/
theorem ideal_divisor_product_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Ideal (𝓞 K), A ≠ 0 →
      (∏ P ∈ (normalizedFactors A).toFinset,
        ((normalizedFactors A).count P + 1 : ℝ)) ≤ C * (Ideal.absNorm A : ℝ) ^ ε := by
  classical
  let b : ℝ := (2 : ℝ) ^ ε
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := b / (b - 1)
  have hc1 : 1 ≤ c := (one_le_div (by linarith : (0 : ℝ) < b - 1)).mpr (by linarith)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  obtain ⟨M, hM⟩ := exists_large_base_threshold hε
  let small : Finset (Ideal (𝓞 K)) := (Ideal.finite_setOf_absNorm_le M).toFinset
  refine ⟨c ^ small.card, by positivity, ?_⟩
  intro A hA
  let F := (normalizedFactors A).toFinset
  have hlocal : ∀ P ∈ F,
      ((normalizedFactors A).count P : ℝ) + 1 ≤
        (if Ideal.absNorm P < M then c else 1) *
          ((Ideal.absNorm P : ℝ) ^ ε) ^ (normalizedFactors A).count P := by
    intro P hP
    have hp2 : (2 : ℝ) ≤ Ideal.absNorm P := by
      exact_mod_cast ideal_factor_norm_ge_two A P (Multiset.mem_toFinset.mp hP)
    have hbp : b ≤ (Ideal.absNorm P : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) hp2 hε.le
    by_cases hsmall : Ideal.absNorm P < M
    · rw [if_pos hsmall]
      exact (multiplicity_le_geometric b hb _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbp _) hc0.le)
    · rw [if_neg hsmall, one_mul]
      have hv : ((normalizedFactors A).count P : ℝ) + 1 ≤
          (2 : ℝ) ^ (normalizedFactors A).count P := by
        exact_mod_cast (Nat.lt_two_pow_self (n := (normalizedFactors A).count P))
      exact hv.trans (pow_le_pow_left₀ (by norm_num)
        (hM (Ideal.absNorm P) (Nat.le_of_not_gt hsmall)) _)
  have hconstant : (∏ P ∈ F, if Ideal.absNorm P < M then c else 1) ≤ c ^ small.card := by
    rw [← Finset.prod_filter (fun P => Ideal.absNorm P < M) (fun _ => c), Finset.prod_const]
    apply pow_le_pow_right₀ hc1
    apply Finset.card_le_card
    intro P hP
    have hnorm := (Finset.mem_filter.mp hP).2
    exact (Ideal.finite_setOf_absNorm_le M).mem_toFinset.mpr (Nat.le_of_lt hnorm)
  calc
    _ ≤ ∏ P ∈ F, (if Ideal.absNorm P < M then c else 1) *
        ((Ideal.absNorm P : ℝ) ^ ε) ^ (normalizedFactors A).count P := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro P hP
      exact hlocal P hP
    _ = (∏ P ∈ F, if Ideal.absNorm P < M then c else 1) * (Ideal.absNorm A : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, ideal_factor_norm_rpow A hA]
    _ ≤ c ^ small.card * (Ideal.absNorm A : ℝ) ^ ε :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)

theorem ideal_divisor_finset_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Ideal (𝓞 K)), A ≠ 0 →
      ∀ S : Finset (Ideal (𝓞 K)), (∀ J ∈ S, J ∣ A) →
        (S.card : ℝ) ≤ C * (Ideal.absNorm A : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := ideal_divisor_product_le_rpow (K := K) hε
  refine ⟨C, hC, ?_⟩
  intro A hA S hS
  have hcard := ideal_divisor_card_le_product A hA S hS
  have hcast : (S.card : ℝ) ≤ ∏ P ∈ (normalizedFactors A).toFinset,
      ((normalizedFactors A).count P + 1 : ℝ) := by exact_mod_cast hcard
  exact hcast.trans (hbound A hA)

def idealDivisors (A : Ideal (𝓞 K)) : Set (Ideal (𝓞 K)) := {J | J ∣ A}

theorem idealDivisors_finite (A : Ideal (𝓞 K)) (hA : A ≠ 0) :
    (idealDivisors A).Finite := by
  apply (Ideal.finite_setOf_absNorm_le (Ideal.absNorm A)).subset
  intro J hJ
  have hpos : 0 < Ideal.absNorm A :=
    Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hA)
  exact Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hJ)

/-- The actual set of all ideal divisors has a uniform epsilon bound. -/
theorem ideal_divisor_count_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Ideal (𝓞 K), A ≠ 0 →
      ((idealDivisors A).ncard : ℝ) ≤ C * (Ideal.absNorm A : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := ideal_divisor_finset_bound (K := K) hε
  refine ⟨C, hC, ?_⟩
  intro A hA
  have hf := idealDivisors_finite A hA
  rw [Set.ncard_eq_toFinset_card _ hf]
  exact hbound A hA hf.toFinset (fun J hJ => hf.mem_toFinset.mp hJ)

end WaringSiegel.IdealDivisorBounds
