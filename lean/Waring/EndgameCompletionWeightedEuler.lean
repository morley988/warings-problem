import Waring.EndgameCompletionEuler

/-!
# A polynomial weight in the complete-coefficient Euler series

The already proved good-prime block estimate has a `p⁻²` base. Weighting
the modulus by `q^(1/(2k))` changes this to `p⁻³ᐟ²`, which is still
summable over primes. Exceptional prime-power series retain a geometric
ratio at most one half. This supplies a quantitative pruning tail.
-/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion

def pruningDecay (k : ℕ) : ℝ := (2*(k : ℝ))⁻¹

theorem pruningDecay_pos {k : ℕ} (hk : 0<k) : 0<pruningDecay k := by
  unfold pruningDecay
  positivity

theorem pruningDecay_mul {k : ℕ} (hk : 0<k) : (k : ℝ)*pruningDecay k=1/2 := by
  have hkR : (k : ℝ)≠0 := by exact_mod_cast hk.ne'
  unfold pruningDecay
  field_simp

def weightedCompleteCoefficient (k s q : ℕ) : ℝ :=
  (q : ℝ)^(pruningDecay k)*completeCoefficient k s q

theorem weightedCompleteCoefficient_nonneg (k s q : ℕ) :
    0≤weightedCompleteCoefficient k s q :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (completeCoefficient_nonneg k s q)

@[simp] theorem weightedCompleteCoefficient_zero (k s : ℕ) :
    weightedCompleteCoefficient k s 0=0 := by simp [weightedCompleteCoefficient]

@[simp] theorem weightedCompleteCoefficient_one (k s : ℕ) :
    weightedCompleteCoefficient k s 1=1 := by simp [weightedCompleteCoefficient]

theorem weightedCompleteCoefficient_coprime (k s : ℕ) (hk : 0<k)
    {m n : ℕ} (hmn : m.Coprime n) :
    weightedCompleteCoefficient k s (m*n)=
      weightedCompleteCoefficient k s m*weightedCompleteCoefficient k s n := by
  rw [weightedCompleteCoefficient,completeCoefficient_coprime k s hk hmn,Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  unfold weightedCompleteCoefficient
  ring

def weightedPrimePowerMoment (p : ℕ) [Fact p.Prime] (k s l : ℕ) : ℝ :=
  ((p^l : ℕ) : ℝ)^(pruningDecay k)*primePowerMoment p k s l

theorem weightedCompleteCoefficient_primepower {p : ℕ} [Fact p.Prime] (k s l : ℕ) :
    weightedCompleteCoefficient k s (p^l)=weightedPrimePowerMoment p k s l := by
  rw [weightedCompleteCoefficient,completeCoefficient_primepower]
  rfl

@[simp] theorem weightedPrimePowerMoment_zero {p : ℕ} [Fact p.Prime] (k s : ℕ) :
    weightedPrimePowerMoment p k s 0=1 := by
  simp [weightedPrimePowerMoment,primePowerMoment_zero]

theorem weighted_prime_block_power {p : ℕ} [Fact p.Prime]
    (k u v : ℕ) (hk : 0<k) (hv : v≤k) :
    ((p^(u*k+v) : ℕ) : ℝ)^(pruningDecay k)≤
      (p : ℝ)^(1/2 : ℝ)*((p : ℝ)^(1/2 : ℝ))^u := by
  have hp : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hδ := (pruningDecay_pos hk).le
  have hkd := pruningDecay_mul hk
  have hvd : (v : ℝ)*pruningDecay k≤1/2 := by
    rw [← hkd]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hv) hδ
  rw [Nat.cast_pow,← Real.rpow_natCast (p : ℝ) (u*k+v),← Real.rpow_mul hp.le,
    ← Real.rpow_mul_natCast hp.le (1/2 : ℝ) u,← Real.rpow_add hp]
  apply Real.rpow_le_rpow_of_exponent_le hp1
  push_cast
  calc
    _ = (u : ℝ)*((k : ℝ)*pruningDecay k)+(v : ℝ)*pruningDecay k := by ring
    _ ≤ (u : ℝ)*(1/2)+(1/2) := by rw [hkd]; gcongr
    _ = _ := by ring

def weightedPrimeRatio (p k s : ℕ) : ℝ :=
  (p : ℝ)^(1/2 : ℝ)*((p : ℝ)^k/(p : ℝ)^s)

theorem weightedPrimeRatio_le_half {p : ℕ} [Fact p.Prime]
    (k s : ℕ) (hks : k+2≤s) : weightedPrimeRatio p k s≤1/2 := by
  have hp : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp2 : (2 : ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hroot : (p : ℝ)^(1/2 : ℝ)≤p := by
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ)≤p)
      (by norm_num : (1/2 : ℝ)≤1)).trans_eq (Real.rpow_one _)
  calc
    _ ≤ (p : ℝ)*(1/(p : ℝ)^2) :=
      mul_le_mul hroot (primepower_ratio_le_inv_sq (p := p) k s hks) (by positivity) hp.le
    _ = 1/(p : ℝ) := by field_simp
    _ ≤ 1/2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2

theorem weightedPrimeRatio_nonneg (p k s : ℕ) : 0≤weightedPrimeRatio p k s := by
  unfold weightedPrimeRatio
  positivity

theorem weightedPrimePowerMoment_good_blocks {p : ℕ} [Fact p.Prime]
    (k s u v : ℕ) (hk : 2≤k) (hs : 6≤s) (hks : k+2≤s)
    (hv : 1≤v) (hvk : v≤k) (hpk : ¬p∣k) :
    weightedPrimePowerMoment p k s (u*k+v)≤
      (8*(k : ℝ)^6*(p : ℝ)^(1/2 : ℝ)/(p : ℝ)^2)*
        weightedPrimeRatio p k s^u := by
  have hh := mul_le_mul (weighted_prime_block_power k u v (by omega) hvk)
    (primitiveCompleteMoment_good_blocks_le k s u v hk hs hks hv hvk hpk)
    (primitiveCompleteMoment_nonneg ..)
    (by positivity : 0≤(p : ℝ)^(1/2 : ℝ)*((p : ℝ)^(1/2 : ℝ))^u)
  apply hh.trans_eq
  unfold weightedPrimeRatio
  rw [mul_pow]
  ring

theorem weightedPrimePowerMoment_blocks {p : ℕ} [Fact p.Prime]
    (k s u v : ℕ) (hk : 1≤k) (hv : 1≤v) (hvk : v≤k)
    (hrec : PrimePowerRecurrence p k) :
    weightedPrimePowerMoment p k s (u*k+v)≤
      ((p : ℝ)^(1/2 : ℝ)*(p : ℝ)^k)*weightedPrimeRatio p k s^u := by
  have hh := mul_le_mul (weighted_prime_block_power k u v (by omega) hvk)
    (primitiveCompleteMoment_blocks_trivial_le k s u v hk (by omega) hvk hrec)
    (primitiveCompleteMoment_nonneg ..)
    (by positivity : 0≤(p : ℝ)^(1/2 : ℝ)*((p : ℝ)^(1/2 : ℝ))^u)
  apply hh.trans_eq
  unfold weightedPrimeRatio
  rw [mul_pow]
  ring

theorem weightedPrimePowerMoment_nonneg {p : ℕ} [Fact p.Prime] (k s l : ℕ) :
    0≤weightedPrimePowerMoment p k s l :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (primitiveCompleteMoment_nonneg ..)

theorem weightedPrimePowerMoment_good_tail {p : ℕ} [Fact p.Prime]
    (k s : ℕ) (hk : 2≤k) (hs : 6≤s) (hks : k+2≤s) (hpk : ¬p∣k) :
    Summable (fun l=>weightedPrimePowerMoment p k s (l+1)) ∧
      (∑' l : ℕ,weightedPrimePowerMoment p k s (l+1))≤
        16*(k : ℝ)^7/(p : ℝ)^(3/2 : ℝ) := by
  have hp : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hr := weightedPrimeRatio_le_half (p := p) k s hks
  have hh := summable_tail_of_block_bound (weightedPrimePowerMoment p k s) k (by omega)
    (C := 8*(k : ℝ)^6*(p : ℝ)^(1/2 : ℝ)/(p : ℝ)^2)
    (ρ := weightedPrimeRatio p k s) (by positivity)
    (weightedPrimeRatio_nonneg p k s) (by linarith)
    (weightedPrimePowerMoment_nonneg k s)
    (fun u v=>weightedPrimePowerMoment_good_blocks k s u (v.val+1) hk hs hks
      (by omega) (by omega) hpk)
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ (k : ℝ)*(8*(k : ℝ)^6*(p : ℝ)^(1/2 : ℝ)/(p : ℝ)^2)/(1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ = _ := by
      have he : (p : ℝ)^(1/2 : ℝ)*(p : ℝ)^(3/2 : ℝ)=(p : ℝ)^2 := by
        rw [← Real.rpow_add hp]
        norm_num [Real.rpow_natCast]
      field_simp
      rw [← he]
      ring

theorem weightedPrimePowerMoment_tail {p : ℕ} [Fact p.Prime]
    (k s : ℕ) (hk : 1≤k) (hks : k+2≤s) (hrec : PrimePowerRecurrence p k) :
    Summable (fun l=>weightedPrimePowerMoment p k s (l+1)) ∧
      (∑' l : ℕ,weightedPrimePowerMoment p k s (l+1))≤2*(k : ℝ)*(p : ℝ)^(k+1) := by
  have hp : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hr := weightedPrimeRatio_le_half (p := p) k s hks
  have hroot : (p : ℝ)^(1/2 : ℝ)≤p :=
    (Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num : (1/2 : ℝ)≤1)).trans_eq (Real.rpow_one _)
  have hh := summable_tail_of_block_bound (weightedPrimePowerMoment p k s) k (by omega)
    (C := (p : ℝ)^(1/2 : ℝ)*(p : ℝ)^k) (ρ := weightedPrimeRatio p k s)
    (by positivity) (weightedPrimeRatio_nonneg p k s) (by linarith)
    (weightedPrimePowerMoment_nonneg k s)
    (fun u v=>weightedPrimePowerMoment_blocks k s u (v.val+1) hk
      (by omega) (by omega) hrec)
  refine ⟨hh.1,hh.2.trans ?_⟩
  calc
    _ ≤ (k : ℝ)*((p : ℝ)^(1/2 : ℝ)*(p : ℝ)^k)/(1/2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    _ ≤ (k : ℝ)*((p : ℝ)*(p : ℝ)^k)/(1/2) := by gcongr
    _ = _ := by rw [pow_succ]; ring

#print axioms weightedPrimePowerMoment_good_tail
#print axioms weightedPrimePowerMoment_tail

theorem weightedCompleteCoefficient_summable_of_recurrence (k s : ℕ)
    (hk : 2≤k) (hs : 6≤s) (hks : k+2≤s)
    (hrec : ∀ (p : ℕ) (hp : p.Prime),@PrimePowerRecurrence p k ⟨hp⟩) :
    Summable (weightedCompleteCoefficient k s) := by
  let D : ℝ := 16*(k : ℝ)^7
  let E : ℝ := 2*(k : ℝ)*(k : ℝ)^(k+1)
  let b := fun n : ℕ=>D/(n : ℝ)^(3/2 : ℝ)+if n≤k then E else 0
  have hb (n : ℕ) : 0≤b n := by dsimp [b,D,E]; split_ifs <;> positivity
  have hbsum : Summable b := by
    have hpseries : Summable (fun n : ℕ=>D/(n : ℝ)^(3/2 : ℝ)) := by
      simpa only [mul_one_div] using
        (Real.summable_one_div_nat_rpow.mpr (by norm_num : 1<(3/2 : ℝ))).mul_left D
    have hfinite : Summable (fun n : ℕ=>if n≤k then E else 0) := by
      apply summable_of_ne_finset_zero (s := Finset.range (k+1))
      intro n hn
      rw [if_neg]
      simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn
    exact hpseries.add hfinite
  have hlocal (p : ℕ) (hp : p.Prime) :
      Summable (fun l : ℕ=>weightedCompleteCoefficient k s (p^l)) := by
    letI : Fact p.Prime := ⟨hp⟩
    have hh := (weightedPrimePowerMoment_tail k s (by omega) hks (hrec p hp)).1
    have hall : Summable (weightedPrimePowerMoment p k s) := (summable_nat_add_iff 1).mp hh
    simpa only [weightedCompleteCoefficient_primepower] using hall
  apply summable_multiplicative_of_local_bound (weightedCompleteCoefficient k s) b
    (weightedCompleteCoefficient_zero k s) (weightedCompleteCoefficient_one k s)
    (weightedCompleteCoefficient_coprime k s (by omega))
    (weightedCompleteCoefficient_nonneg k s) hb hbsum hlocal
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  have htail := weightedPrimePowerMoment_tail k s (by omega) hks (hrec p hp)
  have hsum : (∑' l : ℕ,weightedCompleteCoefficient k s (p^l))=
      1+∑' l : ℕ,weightedPrimePowerMoment p k s (l+1) := by
    simp only [weightedCompleteCoefficient_primepower]
    have heq := htail.1.sum_add_tsum_nat_add' (f := weightedPrimePowerMoment p k s)
    simpa only [Finset.sum_range_one,weightedPrimePowerMoment_zero] using heq.symm
  rw [hsum]
  apply add_le_add_left
  by_cases hpk : p≤k
  · have hpow : (p : ℝ)^(k+1)≤(k : ℝ)^(k+1) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hpk) _
    have hlarge : 2*(k : ℝ)*(p : ℝ)^(k+1)≤E :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    dsimp [b]
    rw [if_pos hpk]
    exact htail.2.trans (hlarge.trans (le_add_of_nonneg_left (by dsimp [D]; positivity)))
  · have hndiv : ¬p∣k := fun hd=>hpk (Nat.le_of_dvd (by omega) hd)
    have hgood := (weightedPrimePowerMoment_good_tail k s hk hs hks hndiv).2
    simpa only [b,if_neg hpk,add_zero,D] using hgood

theorem degree8_weightedCompleteCoefficient_summable (s : ℕ) (hs : 10≤s) :
    Summable (weightedCompleteCoefficient 8 s) := by
  apply weightedCompleteCoefficient_summable_of_recurrence 8 s
    (by norm_num) (by omega) (by omega)
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact primePowerRecurrence_eight

theorem degree9_weightedCompleteCoefficient_summable (s : ℕ) (hs : 11≤s) :
    Summable (weightedCompleteCoefficient 9 s) := by
  apply weightedCompleteCoefficient_summable_of_recurrence 9 s
    (by norm_num) (by omega) (by omega)
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  exact primePowerRecurrence_nine

theorem completeCoefficient_tail_pointwise (k s N q : ℕ) (hk : 0<k) (hN : 1≤N) :
    (if N≤q then completeCoefficient k s q else 0)≤
      (N : ℝ)^(-pruningDecay k)*weightedCompleteCoefficient k s q := by
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hd := (pruningDecay_pos hk).le
  split_ifs with hNq
  · have hnum : (N : ℝ)^(pruningDecay k)*completeCoefficient k s q≤
        weightedCompleteCoefficient k s q :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hn.le (by exact_mod_cast hNq) hd) (completeCoefficient_nonneg ..)
    have hh := mul_le_mul_of_nonneg_left hnum
      (inv_nonneg.mpr (Real.rpow_nonneg hn.le (pruningDecay k)))
    rw [← mul_assoc,inv_mul_cancel₀ (Real.rpow_pos_of_pos hn _).ne',one_mul] at hh
    simpa only [Real.rpow_neg hn.le] using hh
  · exact mul_nonneg (Real.rpow_nonneg hn.le _) (weightedCompleteCoefficient_nonneg ..)

/-- Quantitative denominator tail with the fixed decay `1/(2k)`. -/
theorem completeCoefficient_tail_le (k s N : ℕ) (hk : 0<k) (hN : 1≤N)
    (hsum : Summable (weightedCompleteCoefficient k s)) :
    (∑' q : ℕ,if N≤q then completeCoefficient k s q else 0)≤
      (N : ℝ)^(-pruningDecay k)*(∑' q : ℕ,weightedCompleteCoefficient k s q) := by
  have hmajor := hsum.mul_left ((N : ℝ)^(-pruningDecay k))
  have hnonneg (q : ℕ) : 0≤(if N≤q then completeCoefficient k s q else 0) := by
    split_ifs <;> first | exact completeCoefficient_nonneg .. | positivity
  have htail := Summable.of_nonneg_of_le hnonneg (completeCoefficient_tail_pointwise k s N · hk hN) hmajor
  simpa only [tsum_mul_left] using
    htail.tsum_le_tsum (completeCoefficient_tail_pointwise k s N · hk hN) hmajor

#print axioms degree8_weightedCompleteCoefficient_summable
#print axioms degree9_weightedCompleteCoefficient_summable
#print axioms completeCoefficient_tail_le
end Waring.EndgameCompletion
