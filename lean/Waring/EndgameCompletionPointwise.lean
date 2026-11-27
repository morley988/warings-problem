import Waring.EndgameCompletionEuler
import Waring.EndgameCompletionTwistedCRT

/-!
# Primitive pointwise monomial complete-sum bounds

The exact prime-power recurrence, the proved prime second moment, and CRT
give normalized decay q^(-1/k+epsilon). Singular primes are absorbed through
the elementary bound p<=k, not through any unproved exponential-sum theorem.
-/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion

theorem normalizedCompleteSum_small_degree_power {p : ℕ} [Fact p.Prime]
    (k v a : ℕ) (hk : 2≤k) (hv : 1≤v) (hvk : v≤k) (ha : ¬p∣a) :
    (normalizedCompleteSum (p^v) k (a : ZMod (p^v)))^k≤
      ((2*k^2 : ℕ) : ℝ)^k/(p : ℝ)^v := by
  have hp : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hk1 : (1 : ℝ)≤k := by exact_mod_cast (show 1≤k by omega)
  have hD : (1 : ℝ)≤((2*k^2 : ℕ) : ℝ) := by push_cast; nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hDpow : ((2*k^2 : ℕ) : ℝ)≤((2*k^2 : ℕ) : ℝ)^k := by
    simpa only [pow_one] using pow_le_pow_right₀ hD (show 1≤k by omega)
  by_cases hpk : p∣k
  · have hple : (p : ℝ)≤k := by exact_mod_cast Nat.le_of_dvd (show 0<k by omega) hpk
    have hpD : (p : ℝ)≤((2*k^2 : ℕ) : ℝ) := by push_cast; nlinarith [sq_nonneg ((k : ℝ)-1)]
    have hpv : (p : ℝ)^v≤((2*k^2 : ℕ) : ℝ)^k :=
      (pow_le_pow_right₀ hp1 hvk).trans (pow_le_pow_left₀ hp.le hpD k)
    exact (pow_le_one₀ (normalizedCompleteSum_nonneg ..) (normalizedCompleteSum_le_one ..)).trans
      ((one_le_div (pow_pos hp v)).mpr hpv)
  · by_cases hv1 : v=1
    · subst v
      rw [normalizedCompleteSum_nat_congr_modulus (p^1) p k a (pow_one p),pow_one]
      let u : (ZMod p)ˣ := ZMod.unitOfCoprime a
        ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr ha).symm
      have hu : (u : ZMod p)=(a : ZMod p) := ZMod.coe_unitOfCoprime _ _
      calc
        _ ≤ (normalizedCompleteSum p k (a : ZMod p))^2 :=
          pow_le_pow_of_le_one (normalizedCompleteSum_nonneg ..) (normalizedCompleteSum_le_one ..) hk
        _ ≤ 2*(k : ℝ)^2/p := by rw [← hu]; exact normalizedCompleteSum_prime_sq_le k (by omega) u
        _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using hDpow) hp.le
    · rw [normalizedCompleteSum_primepower_small_nat v k a (by omega) hvk ha hpk,div_pow,one_pow]
      calc
        _ ≤ 1/(p : ℝ)^v := one_div_le_one_div_of_le (pow_pos hp v) (pow_le_pow_right₀ hp1 hvk)
        _ ≤ _ := div_le_div_of_nonneg_right (one_le_pow₀ hD) (pow_nonneg hp.le _)

theorem normalizedCompleteSum_primepower_degree_power {p : ℕ} [Fact p.Prime]
    (k l a : ℕ) (hk : 2≤k) (hl : 1≤l) (hrec : PrimePowerRecurrence p k) (ha : ¬p∣a) :
    (normalizedCompleteSum (p^l) k (a : ZMod (p^l)))^k≤
      ((2*k^2 : ℕ) : ℝ)^k/(p : ℝ)^l := by
  let u := (l-1)/k
  let v := (l-1)%k+1
  have hv : 1≤v := by omega
  have hvk : v≤k := by have := Nat.mod_lt (l-1) (show 0<k by omega); omega
  have he : u*k+v=l := by
    calc
      _ = ((l-1)%k+k*((l-1)/k))+1 := by dsimp [u,v]; ring
      _ = (l-1)+1 := by rw [Nat.mod_add_div]
      _ = l := Nat.sub_add_cancel hl
  rw [← he,normalizedCompleteSum_primepower_blocks k u v a (by omega) hrec ha,mul_pow]
  calc
    _ ≤ ((1/(p : ℝ))^u)^k*(((2*k^2 : ℕ) : ℝ)^k/(p : ℝ)^v) :=
      mul_le_mul_of_nonneg_left (normalizedCompleteSum_small_degree_power k v a hk hv hvk ha) (by positivity)
    _ = _ := by
      simp only [← pow_mul,pow_add,div_pow,one_pow,div_eq_mul_inv,mul_inv_rev]
      ring

theorem normalizedCompleteSum_degree_power_omega (k : ℕ) (hk : 2≤k)
    (hrec : ∀ (p : ℕ) [Fact p.Prime],PrimePowerRecurrence p k)
    (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    (normalizedCompleteSum q k a)^k≤((2*k^2 : ℕ) : ℝ)^(k*q.primeFactors.card)/(q : ℝ) := by
  suffices H : ∀ q (hq : q≠0),letI : NeZero q := ⟨hq⟩
      ∀ a : (ZMod q)ˣ,(normalizedCompleteSum q k a)^k≤
        ((2*k^2 : ℕ) : ℝ)^(k*q.primeFactors.card)/(q : ℝ) by
    exact H q (NeZero.ne q) a
  intro q
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p l hp hl =>
      intro hq
      letI : Fact p.Prime := ⟨hp⟩
      letI : NeZero (p^l) := ⟨hq⟩
      intro a
      have hh := normalizedCompleteSum_primepower_degree_power k l (a : ZMod (p^l)).val
        hk (by omega) (hrec p) (prime_not_dvd_unit_val l hl a)
      simpa only [ZMod.natCast_zmod_val,Nat.primeFactors_pow p hl.ne',hp.primeFactors,
        Finset.card_singleton,Nat.mul_one,Nat.cast_pow] using hh
  | zero => intro hq; exact False.elim (hq rfl)
  | one =>
      intro _ a
      simp [normalizedCompleteSum,completeMonomialSumMod_one]
  | coprime q r hq hr hqr ihq ihr =>
      intro hqr0
      letI : NeZero q := ⟨by omega⟩
      letI : NeZero r := ⟨by omega⟩
      letI : NeZero (q*r) := ⟨hqr0⟩
      intro a
      let aq := (coprimeUnitsEquiv q r hqr a).1*(ZMod.unitOfCoprime r hqr.symm)^(k-1)
      let ar := (coprimeUnitsEquiv q r hqr a).2*(ZMod.unitOfCoprime q hqr)^(k-1)
      have Hq := ihq (NeZero.ne q) aq
      have Hr := ihr (NeZero.ne r) ar
      rw [normalizedCompleteSum_coprime_units q r k hqr (by omega),mul_pow]
      apply (mul_le_mul Hq Hr (pow_nonneg (normalizedCompleteSum_nonneg r k ar) k)
        (div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg q))).trans_eq
      have hcard : (q*r).primeFactors.card=q.primeFactors.card+r.primeFactors.card := by
        rw [hqr.primeFactors_mul,Finset.card_union_of_disjoint hqr.disjoint_primeFactors]
      simp only [hcard,Nat.mul_add,pow_add,Nat.cast_mul,div_eq_mul_inv,mul_inv_rev]
      ring

theorem normalizedCompleteSum_omega_le (k : ℕ) (hk : 2≤k)
    (hrec : ∀ (p : ℕ) [Fact p.Prime],PrimePowerRecurrence p k)
    (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    normalizedCompleteSum q k a≤
      ((2*k^2 : ℕ) : ℝ)^q.primeFactors.card*(q : ℝ)^(-1/(k : ℝ)) := by
  have hq : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  have hk0 : (k : ℝ)≠0 := by exact_mod_cast (show k≠0 by omega)
  apply (pow_le_pow_iff_left₀ (normalizedCompleteSum_nonneg ..) (by positivity) (show k≠0 by omega)).mp
  calc
    _ ≤ ((2*k^2 : ℕ) : ℝ)^(k*q.primeFactors.card)/(q : ℝ) :=
      normalizedCompleteSum_degree_power_omega k hk hrec q a
    _ = _ := by
      rw [mul_pow,← pow_mul,← Real.rpow_mul_natCast hq.le,
        div_mul_cancel₀ _ hk0,Real.rpow_neg_one]
      rw [Nat.mul_comm q.primeFactors.card k]
      rfl

theorem normalizedCompleteSum_divisor_le (k : ℕ) (hk : 2≤k)
    (hrec : ∀ (p : ℕ) [Fact p.Prime],PrimePowerRecurrence p k)
    (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    normalizedCompleteSum q k a≤(q.divisors.card : ℝ)^(2*k^2)*(q : ℝ)^(-1/(k : ℝ)) := by
  have hc : (2*k^2)^q.primeFactors.card≤q.divisors.card^(2*k^2) := by
    calc
      _ ≤ (2^(2*k^2))^q.primeFactors.card := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = (2^q.primeFactors.card)^(2*k^2) := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_left
        (PolicyCompletionRoots.two_pow_primeFactors_card_le_divisors (NeZero.pos q)) _
  exact (normalizedCompleteSum_omega_le k hk hrec q a).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem normalizedCompleteSum_le_rpow_of_recurrence (k : ℕ) (hk : 2≤k)
    (hrec : ∀ (p : ℕ) [Fact p.Prime],PrimePowerRecurrence p k)
    {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      normalizedCompleteSum q k a≤C*(q : ℝ)^(-1/(k : ℝ)+ε) := by
  obtain ⟨C,hC,hdiv⟩ := AuxiliaryL2Grouping.divisor_power_le_rpow (2*k^2) hε
  refine ⟨C,hC,?_⟩
  intro q _ a
  have hq : (0 : ℝ)<q := by exact_mod_cast NeZero.pos q
  calc
    _ ≤ (q.divisors.card : ℝ)^(2*k^2)*(q : ℝ)^(-1/(k : ℝ)) :=
      normalizedCompleteSum_divisor_le k hk hrec q a
    _ ≤ (C*(q : ℝ)^ε)*(q : ℝ)^(-1/(k : ℝ)) :=
      mul_le_mul_of_nonneg_right (hdiv q (NeZero.pos q)) (by positivity)
    _ = _ := by rw [Real.rpow_add hq]; ring

theorem degree8_normalizedCompleteSum_pointwise {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      normalizedCompleteSum q 8 a≤C*(q : ℝ)^(-(1/8 : ℝ)+ε) := by
  have hh := normalizedCompleteSum_le_rpow_of_recurrence 8 (by norm_num)
    (fun p hp=>@primePowerRecurrence_eight p hp) hε
  simpa only [Nat.cast_ofNat,neg_div] using hh

theorem degree9_normalizedCompleteSum_pointwise {ε : ℝ} (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ),
      normalizedCompleteSum q 9 a≤C*(q : ℝ)^(-(1/9 : ℝ)+ε) := by
  have hh := normalizedCompleteSum_le_rpow_of_recurrence 9 (by norm_num)
    (fun p hp=>@primePowerRecurrence_nine p hp) hε
  simpa only [Nat.cast_ofNat,neg_div] using hh

#print axioms degree8_normalizedCompleteSum_pointwise
#print axioms degree9_normalizedCompleteSum_pointwise
end Waring.EndgameCompletion
