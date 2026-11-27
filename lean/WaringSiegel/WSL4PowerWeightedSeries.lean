import WaringSiegel.WSL4PowerWeightedBase

/-! # A uniform weighted local conductor mass for every positive degree -/
noncomputable section
set_option maxHeartbeats 1600000
open IsLocalRing Filter Topology
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {R:Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem weightedPowerIncrement_scaling (k p:ℕ) (hk:0<k) (hkp:k+1≤p)
    {a b:R} (n:ℕ)
    (he:normalizedLocalPowerCount R k p (n+k+1) a-normalizedLocalPowerCount R k p (n+k) a=
      (1/(Nat.card (ResidueField R):ℝ)^(p-k))*
        (normalizedLocalPowerCount R k p (n+1) b-normalizedLocalPowerCount R k p n b)) :
    weightedPowerIncrement R k p a (n+k)=
      (1/(Nat.card (ResidueField R):ℝ)^(p-k-1))*weightedPowerIncrement R k p b n := by
  have hq:(Nat.card (ResidueField R):ℝ)≠0 := by exact_mod_cast Nat.card_pos.ne'
  unfold weightedPowerIncrement
  rw [powerConductorWeight_add_degree k hk,he,abs_mul,
    abs_of_nonneg (by positivity : 0≤1/(Nat.card (ResidueField R):ℝ)^(p-k))]
  rw [show p-k=(p-k-1)+1 by omega,pow_succ]
  field_simp
  simp only [Nat.add_sub_cancel,mul_assoc,mul_left_comm,mul_comm]

theorem weightedPowerIncrement_all_primes_recurrence
    (k p:ℕ) (hk:0<k) (hp:2≤p) (hkp:k+1≤p) (hk0:(k:R)≠0) (a:R) :
    ∃ b:R,∀ n,2*powerDerivativeOrder R k≤n →
      weightedPowerIncrement R k p a (n+k)≤
        (1/(Nat.card (ResidueField R):ℝ)^(p-k-1))*weightedPowerIncrement R k p b n := by
  rcases normalized_power_increment_step k p hk hp (by omega) hk0 a with hz|⟨b,hb⟩
  · refine ⟨a,fun n hn => ?_⟩
    have he:weightedPowerIncrement R k p a (n+k)=0 := by
      unfold weightedPowerIncrement
      rw [hz n hn,abs_zero,mul_zero]
    rw [he]
    exact mul_nonneg (by positivity) (weightedPowerIncrement_nonneg k p a n)
  · exact ⟨b,fun n hn => (weightedPowerIncrement_scaling k p hk hkp n (hb n hn)).le⟩

theorem power_weighted_singular_ratio_le_half (k p:ℕ) (hkp:k+2≤p) :
    1/(Nat.card (ResidueField R):ℝ)^(p-k-1)≤(1/2:ℝ) := by
  have hq2:2≤(Nat.card (ResidueField R):ℝ) := by
    letI := Fintype.ofFinite (ResidueField R)
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (show 2≤Fintype.card (ResidueField R) from Fintype.one_lt_card)
  apply one_div_le_one_div_of_le (by norm_num)
  exact hq2.trans (by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (show 1≤(Nat.card (ResidueField R):ℝ) by linarith) (show 1≤p-k-1 by omega)))

theorem weightedPowerIncrement_good_summable_bound
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (hku:IsUnit (k:R)) (a:R) :
    Summable (weightedPowerIncrement R k p a) ∧
      (∑' n,weightedPowerIncrement R k p a n)≤
        4*(k:ℝ)*(((k-1:ℕ):ℝ)^8+1)/(Nat.card (ResidueField R):ℝ)^2 := by
  have hbase:∀ a:R,∀ n,n<0+k →weightedPowerIncrement R k p a n≤
      2*(((k-1:ℕ):ℝ)^8+1)/(Nat.card (ResidueField R):ℝ)^2 := by
    intro a n hn
    exact (weightedPowerIncrement_good_initial k p hk hp hkp hku a n (by omega)).trans_eq (by ring)
  have hrec:∀ a:R,∃ b:R,∀ n,0≤n →weightedPowerIncrement R k p a (n+k)≤
      (1/(Nat.card (ResidueField R):ℝ)^(p-k-1))*weightedPowerIncrement R k p b n := by
    simpa only [powerDerivativeOrder_eq_zero_of_unit k hku,Nat.mul_zero] using
      weightedPowerIncrement_all_primes_recurrence (R:=R) k p hk (by omega) (by omega) hku.ne_zero
  have h := eventual_step_summable_bound (weightedPowerIncrement R k p) 0 k hk
    (2*(((k-1:ℕ):ℝ)^8+1)/(Nat.card (ResidueField R):ℝ)^2)
    (1/(Nat.card (ResidueField R):ℝ)^(p-k-1)) (by positivity) (by positivity)
    (power_weighted_singular_ratio_le_half k p (by omega))
    (weightedPowerIncrement_nonneg k p) hbase hrec a
  refine ⟨h.1,?_⟩
  convert h.2 using 1 <;> simp only [zero_add] <;> ring

def powerBadPrimeWeightedMass (R:Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k:ℕ) : ℝ :=
  2*(2*powerDerivativeOrder R k+k:ℕ)*(Nat.card (ResidueField R):ℝ)^(2*(2*powerDerivativeOrder R k+k))

theorem weightedPowerIncrement_all_primes_summable_bound
    (k p:ℕ) (hk:0<k) (hp:2≤p) (hkp:k+2≤p) (hk0:(k:R)≠0) (a:R) :
    Summable (weightedPowerIncrement R k p a) ∧
      (∑' n,weightedPowerIncrement R k p a n)≤powerBadPrimeWeightedMass R k := by
  exact eventual_step_summable_bound (weightedPowerIncrement R k p) (2*powerDerivativeOrder R k) k hk
    ((Nat.card (ResidueField R):ℝ)^(2*(2*powerDerivativeOrder R k+k)))
    (1/(Nat.card (ResidueField R):ℝ)^(p-k-1)) (by positivity) (by positivity)
    (power_weighted_singular_ratio_le_half k p hkp) (weightedPowerIncrement_nonneg k p)
    (fun a n hn => weightedPowerIncrement_initial_bound k p _ n (by omega) hn a)
    (weightedPowerIncrement_all_primes_recurrence k p hk hp (by omega) hk0) a

#print axioms weightedPowerIncrement_good_summable_bound
#print axioms weightedPowerIncrement_all_primes_summable_bound
end WaringSiegel.WSL4Local
