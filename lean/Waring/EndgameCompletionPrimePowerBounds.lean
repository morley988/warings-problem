import Waring.EndgameCompletionCoefficients

/-!
# Quantitative prime-power coefficient bounds

Exact recursions are normalized and iterated in blocks of the degree.
The coefficient remains an ordinary natural number throughout, so that
primitivity is preserved at every positive residue-ring level.
-/

noncomputable section

open scoped BigOperators

namespace Waring.EndgameCompletion

theorem completeMonomialSumMod_nat_congr_modulus (q r k a : ℕ) [NeZero q] [NeZero r]
    (hqr : q=r) :
    completeMonomialSumMod q k (a : ZMod q) = completeMonomialSumMod r k (a : ZMod r) := by
  subst r
  rfl

theorem normalizedCompleteSum_nat_congr_modulus (q r k a : ℕ) [NeZero q] [NeZero r]
    (hqr : q=r) :
    normalizedCompleteSum q k (a : ZMod q) = normalizedCompleteSum r k (a : ZMod r) := by
  subst r
  rfl

theorem prime_not_dvd_natCast_val {p : ℕ} [Fact p.Prime]
    (l a : ℕ) (hl : 0 < l) (ha : ¬ p ∣ a) :
    ¬ p ∣ (a : ZMod (p^l)).val := by
  rwa [dvd_zmod_val_iff_dvd (dvd_pow_self p (Nat.ne_of_gt hl))]

theorem natCast_val_primepower_reduce {p : ℕ} [Fact p.Prime]
    (l j a : ℕ) (hj : j ≤ l) :
    ((a : ZMod (p^l)).val : ZMod (p^j)) = (a : ZMod (p^j)) := by
  rw [ZMod.natCast_val, ZMod.cast_natCast (pow_dvd_pow p hj)]

theorem normalizedCompleteSum_primepower_step_of_eq {p : ℕ} [Fact p.Prime]
    (k t a : ℕ) (hk : 1 ≤ k)
    (hrec : completeMonomialSumMod (p^(t+k)) k (a : ZMod (p^(t+k))) =
      (p^(k-1) : ℕ)*completeMonomialSumMod (p^t) k (a : ZMod (p^t))) :
    normalizedCompleteSum (p^(t+k)) k (a : ZMod (p^(t+k))) =
      (1/(p : ℝ))*normalizedCompleteSum (p^t) k (a : ZMod (p^t)) := by
  unfold normalizedCompleteSum
  rw [hrec, norm_mul, Complex.norm_natCast]
  push_cast
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpowers : (p : ℝ)^(t+k)=(p : ℝ)^t*p^(k-1)*p := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hk, ← pow_add]
  rw [hpowers]
  field_simp

/-- A reusable finite recursion hypothesis. The degree-eight and
degree-nine instances below have already been proved for every prime. -/
def PrimePowerRecurrence (p k : ℕ) [Fact p.Prime] : Prop :=
  ∀ (l : ℕ), k ≤ l → ∀ (a : ZMod (p^l)), ¬ p ∣ a.val →
    completeMonomialSumMod (p^l) k a =
      (p^(k-1) : ℕ)*completeMonomialSumMod (p^(l-k)) k (a.val : ZMod (p^(l-k)))

theorem primePowerRecurrence_good {p : ℕ} [Fact p.Prime]
    (k : ℕ) (hk : 2 ≤ k) (hpk : ¬ p ∣ k) : PrimePowerRecurrence p k := by
  intro l hl a ha
  exact completeMonomialSumMod_primepower_recurrence_good l k hk hl a ha hpk

theorem primePowerRecurrence_eight {p : ℕ} [Fact p.Prime] : PrimePowerRecurrence p 8 :=
  completeMonomialSumMod_degree8_recurrence

theorem primePowerRecurrence_nine {p : ℕ} [Fact p.Prime] : PrimePowerRecurrence p 9 :=
  completeMonomialSumMod_degree9_recurrence

theorem normalizedCompleteSum_primepower_step {p : ℕ} [Fact p.Prime]
    (k t a : ℕ) (hk : 1 ≤ k) (hrec : PrimePowerRecurrence p k) (ha : ¬ p ∣ a) :
    normalizedCompleteSum (p^(t+k)) k (a : ZMod (p^(t+k))) =
      (1/(p : ℝ))*normalizedCompleteSum (p^t) k (a : ZMod (p^t)) := by
  apply normalizedCompleteSum_primepower_step_of_eq k t a hk
  have hh := hrec (t+k) (by omega) (a : ZMod (p^(t+k)))
    (prime_not_dvd_natCast_val (t+k) a (by omega) ha)
  rw [natCast_val_primepower_reduce (t+k) (t+k-k) a (Nat.sub_le _ _)] at hh
  rw [completeMonomialSumMod_nat_congr_modulus (p^(t+k-k)) (p^t) k a
    (by rw [Nat.add_sub_cancel])] at hh
  exact hh

theorem normalizedCompleteSum_primepower_blocks {p : ℕ} [Fact p.Prime]
    (k u v a : ℕ) (hk : 1 ≤ k) (hrec : PrimePowerRecurrence p k) (ha : ¬ p ∣ a) :
    normalizedCompleteSum (p^(u*k+v)) k (a : ZMod (p^(u*k+v))) =
      (1/(p : ℝ))^u*normalizedCompleteSum (p^v) k (a : ZMod (p^v)) := by
  induction u with
  | zero => rw [Nat.zero_mul, Nat.zero_add, pow_zero, one_mul]
  | succ u ih =>
    have hl : (u+1)*k+v=(u*k+v)+k := by ring
    rw [hl, normalizedCompleteSum_primepower_step k (u*k+v) a hk hrec ha, ih, pow_succ]
    ring

theorem primitiveCompleteMoment_blocks_le {p : ℕ} [Fact p.Prime]
    (k s u v : ℕ) (hk : 1 ≤ k) (hv : 0 < v) (hrec : PrimePowerRecurrence p k)
    {B : ℝ} (hB : 0 ≤ B)
    (hbase : ∀ a : ℕ, ¬ p ∣ a → (normalizedCompleteSum (p^v) k (a : ZMod (p^v)))^s ≤ B) :
    primitiveCompleteMoment (p^(u*k+v)) k s ≤
      (p : ℝ)^v*((p : ℝ)^k/(p : ℝ)^s)^u*B := by
  have hh : primitiveCompleteMoment (p^(u*k+v)) k s ≤
      (p^(u*k+v) : ℕ)*((1/(p : ℝ))^(u*s)*B) := by
    apply primitiveCompleteMoment_le_of_uniform _ k s (by positivity)
    intro a
    have ha := prime_not_dvd_unit_val (u*k+v) (by omega) a
    have heq := normalizedCompleteSum_primepower_blocks k u v
      (a : ZMod (p^(u*k+v))).val hk hrec ha
    rw [ZMod.natCast_zmod_val] at heq
    rw [heq, mul_pow, ← pow_mul]
    exact mul_le_mul_of_nonneg_left (hbase _ ha) (by positivity)
  convert hh using 1
  push_cast
  rw [show u*k=k*u by ring, show u*s=s*u by ring, pow_add, pow_mul, pow_mul]
  simp only [div_pow, one_pow]
  ring

theorem normalizedCompleteSum_prime_nat_moment_le {p : ℕ} [Fact p.Prime]
    (k s a : ℕ) (hk : 0 < k) (hs : 6 ≤ s) (ha : ¬ p ∣ a) :
    (normalizedCompleteSum p k (a : ZMod p))^s ≤ (2*(k : ℝ)^2/(p : ℝ))^3 := by
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime a ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ha).symm
  have hu : (u : ZMod p)=(a : ZMod p) := ZMod.coe_unitOfCoprime _ _
  rw [← hu]
  calc
    _ ≤ (normalizedCompleteSum p k u)^6 :=
      pow_le_pow_of_le_one (normalizedCompleteSum_nonneg ..)
        (normalizedCompleteSum_le_one ..) hs
    _ = ((normalizedCompleteSum p k u)^2)^3 := by ring
    _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) (normalizedCompleteSum_prime_sq_le k hk u) 3

theorem normalizedCompleteSum_primepower_small_nat {p : ℕ} [Fact p.Prime]
    (l k a : ℕ) (hl : 2 ≤ l) (hlk : l ≤ k) (ha : ¬ p ∣ a) (hpk : ¬ p ∣ k) :
    normalizedCompleteSum (p^l) k (a : ZMod (p^l)) = 1/(p : ℝ) := by
  let u : (ZMod (p^l))ˣ := ZMod.unitOfCoprime a
    ((Fact.out : p.Prime).coprime_pow_of_not_dvd ha)
  have hu : (u : ZMod (p^l))=(a : ZMod (p^l)) := ZMod.coe_unitOfCoprime _ _
  rw [← hu]
  exact normalizedCompleteSum_primepower_small l k hl hlk u hpk

theorem primepower_ratio_le_inv_sq {p : ℕ} [Fact p.Prime]
    (v s : ℕ) (hvs : v+2 ≤ s) :
    (p : ℝ)^v/(p : ℝ)^s ≤ 1/(p : ℝ)^2 := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  apply (div_le_div_iff₀ (pow_pos hp0 s) (pow_pos hp0 2)).mpr
  rw [one_mul, ← pow_add]
  exact pow_le_pow_right₀ hp hvs

/-- Every positive prime-power level has the same geometric block bound
at good primes. This is the coefficient estimate used for Euler tails. -/
theorem primitiveCompleteMoment_good_blocks_le {p : ℕ} [Fact p.Prime]
    (k s u v : ℕ) (hk : 2 ≤ k) (hs : 6 ≤ s) (hks : k+2 ≤ s)
    (hv : 1 ≤ v) (hvk : v ≤ k) (hpk : ¬ p ∣ k) :
    primitiveCompleteMoment (p^(u*k+v)) k s ≤
      (8*(k : ℝ)^6/(p : ℝ)^2)*((p : ℝ)^k/(p : ℝ)^s)^u := by
  have hrec := primePowerRecurrence_good k hk hpk
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hD : (1 : ℝ) ≤ 8*(k : ℝ)^6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 6
    norm_num at hh
    linarith
  by_cases hv1 : v=1
  · subst v
    have hb := primitiveCompleteMoment_blocks_le k s u 1 (by omega) (by omega) hrec
      (B := (2*(k : ℝ)^2/(p : ℝ))^3) (by positivity) (by
        intro a ha
        rw [normalizedCompleteSum_nat_congr_modulus (p^1) p k a (pow_one p)]
        exact normalizedCompleteSum_prime_nat_moment_le k s a (by omega) hs ha)
    convert hb using 1
    field_simp
    ring
  · have hb := primitiveCompleteMoment_blocks_le k s u v (by omega) (by omega) hrec
      (B := (1/(p : ℝ))^s) (by positivity) (by
        intro a ha
        rw [normalizedCompleteSum_primepower_small_nat v k a (by omega) hvk ha hpk])
    have hratio := primepower_ratio_le_inv_sq (p := p) v s (by omega)
    calc
      _ ≤ (p : ℝ)^v*((p : ℝ)^k/(p : ℝ)^s)^u*(1/(p : ℝ))^s := hb
      _ = ((p : ℝ)^v/(p : ℝ)^s)*((p : ℝ)^k/(p : ℝ)^s)^u := by
        simp only [div_pow, one_pow]
        ring
      _ ≤ (1/(p : ℝ)^2)*((p : ℝ)^k/(p : ℝ)^s)^u :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hD (by positivity)) (by positivity)

theorem primitiveCompleteMoment_blocks_trivial_le {p : ℕ} [Fact p.Prime]
    (k s u v : ℕ) (hk : 1 ≤ k) (hv : 0 < v) (hvk : v ≤ k)
    (hrec : PrimePowerRecurrence p k) :
    primitiveCompleteMoment (p^(u*k+v)) k s ≤
      (p : ℝ)^k*((p : ℝ)^k/(p : ℝ)^s)^u := by
  have hh := primitiveCompleteMoment_blocks_le k s u v hk hv hrec (B := 1) (by norm_num)
    (fun a _ => pow_le_one₀ (normalizedCompleteSum_nonneg ..) (normalizedCompleteSum_le_one ..))
  rw [mul_one] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le : (1 : ℝ) ≤ p) hvk)
    (by positivity))

#print axioms normalizedCompleteSum_primepower_blocks
#print axioms primePowerRecurrence_eight
#print axioms primePowerRecurrence_nine
#print axioms primitiveCompleteMoment_good_blocks_le
#print axioms primitiveCompleteMoment_blocks_trivial_le

end Waring.EndgameCompletion
