import WaringSiegel.WSL3MomentLocalPowerBranchSeeds

/-! # Actual primitive local-density stabilization at every finite prime -/
noncomputable section
set_option maxHeartbeats 1400000
open IsLocalRing Filter Topology
open scoped BigOperators
namespace WaringSiegel.WSL3

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem primitive_local_power_count_ramified_at
    (k : ℕ) (hk : 0<k) (hk0 : (k:R)≠0) (s r e : ℕ)
    (he : e=(powerDerivativeOrder R k+1+r)+powerDerivativeOrder R k) (a : R) :
    primitiveLocalPowerSolutionCount k R (maximalIdeal R^e)
      (Ideal.pow_le_self (by omega)) (s+1) a=
      Nat.card (PrimitivePowerBranchSeeds k R (s+1) a)*
        Nat.card (ResidueField R)^(s*(r+powerDerivativeOrder R k)+powerDerivativeOrder R k) := by
  subst e
  exact primitive_local_power_count_ramified_exact k hk hk0 s r a

def primitivePowerDensityAllPrimes
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k p : ℕ) (a : R) : ℝ :=
  (Nat.card (PrimitivePowerBranchSeeds k R p a):ℝ)/
    (Nat.card (ResidueField R):ℝ)^((p-2)*powerDerivativeOrder R k+(p-1))

theorem normalized_primitive_local_power_count_ramified_eq
    (k : ℕ) (hk : 0<k) (hk0 : (k:R)≠0) (s n : ℕ)
    (hn : 2*powerDerivativeOrder R k≤n) (a : R) :
    normalizedPrimitiveLocalPowerCount k R (s+2) n a=
      primitivePowerDensityAllPrimes R k (s+2) a := by
  have hq : (Nat.card (ResidueField R):ℝ)≠0 := by exact_mod_cast Nat.card_pos.ne'
  unfold normalizedPrimitiveLocalPowerCount primitivePowerDensityAllPrimes
  rw [show s+2=(s+1)+1 by omega,
    primitive_local_power_count_ramified_at k hk hk0 (s+1)
      (n-2*powerDerivativeOrder R k) (n+1) (by omega)]
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.add_sub_cancel,
    show s+1+1-2=s by omega]
  have he : (s+1)*(n+1)=
      ((s+1)*(n-2*powerDerivativeOrder R k+powerDerivativeOrder R k)+powerDerivativeOrder R k)+
        (s*powerDerivativeOrder R k+(s+1)) := by
    have hn' : n=(n-2*powerDerivativeOrder R k)+2*powerDerivativeOrder R k := by omega
    conv_lhs => rw [hn']
    ring
  rw [he,pow_add]
  field_simp
  simp only [pow_add]
  ring

theorem normalized_primitive_local_power_count_all_primes_tendsto
    (k : ℕ) (hk : 0<k) (hk0 : (k:R)≠0) (s : ℕ) (a : R) :
    Tendsto (fun n => normalizedPrimitiveLocalPowerCount k R (s+2) n a) atTop
      (𝓝 (primitivePowerDensityAllPrimes R k (s+2) a)) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  exact eventually_atTop.mpr ⟨2*powerDerivativeOrder R k,
    fun n hn => (normalized_primitive_local_power_count_ramified_eq k hk hk0 s n hn a).symm⟩

theorem normalized_unit_target_local_power_count_all_primes_eq
    (k : ℕ) (hk : 0<k) (hk0 : (k:R)≠0) (s n : ℕ)
    (hn : 2*powerDerivativeOrder R k≤n) {a : R} (ha : IsUnit a) :
    normalizedLocalPowerCount R k (s+2) (n+1) a=
      primitivePowerDensityAllPrimes R k (s+2) a := by
  have he : normalizedLocalPowerCount R k (s+2) (n+1) a=
      normalizedPrimitiveLocalPowerCount k R (s+2) n a := by
    unfold normalizedLocalPowerCount normalizedPrimitiveLocalPowerCount
    unfold localPowerSolutionCount primitiveLocalPowerSolutionCount
    rw [Nat.card_congr (unitTargetPrimitivePowerSolutionsEquiv k hk _
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) _ ha)]
  rw [he,normalized_primitive_local_power_count_ramified_eq k hk hk0 s n hn a]

theorem normalized_unit_target_local_power_count_all_primes_tendsto
    (k : ℕ) (hk : 0<k) (hk0 : (k:R)≠0) (s : ℕ) {a : R} (ha : IsUnit a) :
    Tendsto (fun e => normalizedLocalPowerCount R k (s+2) e a) atTop
      (𝓝 (primitivePowerDensityAllPrimes R k (s+2) a)) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  apply eventually_atTop.mpr
  refine ⟨2*powerDerivativeOrder R k+1,fun e he => ?_⟩
  have heq : e=(e-1)+1 := by omega
  rw [heq]
  exact (normalized_unit_target_local_power_count_all_primes_eq k hk hk0 s (e-1)
    (by omega) ha).symm

#print axioms normalized_primitive_local_power_count_all_primes_tendsto
#print axioms normalized_unit_target_local_power_count_all_primes_tendsto
end WaringSiegel.WSL3
