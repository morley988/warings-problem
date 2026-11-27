import WaringSiegel.WSL4LocalPowerSingular

/-! # Full local-density stabilization for every positive degree

At every finite prime, including primes dividing the degree, primitive
counts stabilize after the derivative precision. Singular scaling and
induction on the target valuation give full stabilization for each nonzero
target. There is no density-existence premise.
-/
noncomputable section
set_option maxHeartbeats 1400000
open IsLocalRing Filter Topology
open scoped BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem normalized_power_count_eq_of_not_mem_power_ideal
    (k s n : ℕ) (hk0 : ((k+1 : ℕ):R)≠0)
    (hn : 2*powerDerivativeOrder R (k+1)≤n+k)
    {a : R} (ha : a ∉ maximalIdeal R^(k+1)) :
    normalizedLocalPowerCount R (k+1) (s+2) (n+k+1) a =
      primitivePowerDensityAllPrimes R (k+1) (s+2) a := by
  letI := dvr_power_quotient_finite (R:=R) (n+k+1)
  have hc := local_power_count_primitive_add_singular (k+1)
    (maximalIdeal R^(n+k+1)) (Ideal.pow_le_self (by omega)) (s+2) a
  rw [singular_local_power_count_zero k n (s+2) ha, add_zero] at hc
  have he : normalizedLocalPowerCount R (k+1) (s+2) (n+k+1) a =
      normalizedPrimitiveLocalPowerCount (k+1) R (s+2) (n+k) a := by
    unfold normalizedLocalPowerCount normalizedPrimitiveLocalPowerCount
    rw [hc]
  rw [he]
  exact normalized_primitive_local_power_count_ramified_eq
    (k+1) (by omega) hk0 s (n+k) hn a

theorem normalized_power_count_scaling_recurrence_all_primes
    (k s n : ℕ) (hk0 : ((k+1 : ℕ):R)≠0)
    {π : R} (hπ : Irreducible π)
    (hn : 2*powerDerivativeOrder R (k+1)≤n+k) (b : R) :
    normalizedLocalPowerCount R (k+1) (s+2) (n+k+1) (π^(k+1)*b) =
      primitivePowerDensityAllPrimes R (k+1) (s+2) (π^(k+1)*b) +
        normalizedLocalPowerCount R (k+1) (s+2) n b *
          ((Nat.card (ResidueField R):ℝ)^((s+2)*k) /
            (Nat.card (ResidueField R):ℝ)^((s+1)*(k+1))) := by
  letI := dvr_power_quotient_finite (R:=R) (n+k+1)
  have hq : (Nat.card (ResidueField R):ℝ)≠0 := by exact_mod_cast Nat.card_pos.ne'
  have hc := local_power_count_primitive_add_singular (k+1)
    (maximalIdeal R^(n+k+1)) (Ideal.pow_le_self (by omega)) (s+2) (π^(k+1)*b)
  rw [singular_local_power_count_scaled k hπ n (s+2) b] at hc
  have hp := normalized_primitive_local_power_count_ramified_eq
    (k+1) (by omega) hk0 s (n+k) hn (π^(k+1)*b)
  rw [← hp]
  unfold normalizedLocalPowerCount normalizedPrimitiveLocalPowerCount
  rw [hc]
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,add_div]
  congr 1
  have hd : (s+2-1)*(n+k+1)=(s+2-1)*n+(s+1)*(k+1) := by
    have he : s+2-1=s+1 := by omega
    rw [he]
    ring
  rw [hd,pow_add]
  field_simp

theorem unit_mul_uniformizer_pow_not_mem_power_ideal
    {π : R} (hπ : Irreducible π) (u : Rˣ) {t k : ℕ} (ht : t<k) :
    (u:R)*π^t ∉ maximalIdeal R^k := by
  intro hm
  rw [hπ.maximalIdeal_eq,Ideal.span_singleton_pow,Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd,hπ.addVal_pow,
    IsDiscreteValuationRing.addVal_def' u hπ t] at hm
  have hle : k≤t := by exact_mod_cast hm
  omega

theorem normalized_power_count_all_primes_unit_pow_eventually_constant
    (k s : ℕ) (hk0 : ((k+1 : ℕ):R)≠0)
    {π : R} (hπ : Irreducible π) (u : Rˣ) (t : ℕ) :
    ∃ σ : ℝ, ∃ E : ℕ, ∀ e : ℕ,E≤e →
      normalizedLocalPowerCount R (k+1) (s+2) e ((u:R)*π^t)=σ := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t<k+1
    · refine ⟨primitivePowerDensityAllPrimes R (k+1) (s+2) ((u:R)*π^t),
        2*powerDerivativeOrder R (k+1)+(k+1),?_⟩
      intro e he
      have heq : e=(e-(k+1))+k+1 := by omega
      rw [heq]
      exact normalized_power_count_eq_of_not_mem_power_ideal k s (e-(k+1)) hk0
        (by omega) (unit_mul_uniformizer_pow_not_mem_power_ideal hπ u ht)
    · have hkt : k+1≤t := by omega
      obtain ⟨σ,E,hE⟩ := ih (t-(k+1)) (by omega)
      have ha : (u:R)*π^t=π^(k+1)*((u:R)*π^(t-(k+1))) := by
        calc
          (u:R)*π^t=(u:R)*(π^(t-(k+1))*π^(k+1)) := by
            rw [← pow_add,Nat.sub_add_cancel hkt]
          _=π^(k+1)*((u:R)*π^(t-(k+1))) := by ring
      refine ⟨primitivePowerDensityAllPrimes R (k+1) (s+2) ((u:R)*π^t)+
        σ*((Nat.card (ResidueField R):ℝ)^((s+2)*k) /
          (Nat.card (ResidueField R):ℝ)^((s+1)*(k+1))),
        max E (2*powerDerivativeOrder R (k+1))+(k+1),?_⟩
      intro e he
      have heq : e=(e-(k+1))+k+1 := by omega
      rw [heq,ha,normalized_power_count_scaling_recurrence_all_primes
        k s (e-(k+1)) hk0 hπ (by omega),hE (e-(k+1)) (by omega)]

/-- Actual full normalized counts stabilize for every nonzero target and
positive degree, at every finite prime. -/
theorem normalized_power_count_all_primes_eventually_constant_of_ne_zero
    (k p : ℕ) (hk : 0<k) (hp : 2≤p) (hk0 : (k:R)≠0)
    {a : R} (ha : a≠0) :
    ∃ σ : ℝ, ∃ E : ℕ, ∀ e : ℕ,E≤e → normalizedLocalPowerCount R k p e a=σ := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨t,u,rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have hk' : k-1+1=k := by omega
  have hp' : p-2+2=p := by omega
  simpa only [hk',hp'] using normalized_power_count_all_primes_unit_pow_eventually_constant
    (k-1) (p-2) (by simpa only [hk'] using hk0) hπ u t

theorem normalized_power_count_all_primes_tendsto_of_ne_zero
    (k p : ℕ) (hk : 0<k) (hp : 2≤p) (hk0 : (k:R)≠0)
    {a : R} (ha : a≠0) :
    ∃ σ : ℝ,Tendsto (fun e => normalizedLocalPowerCount R k p e a) atTop (𝓝 σ) := by
  obtain ⟨σ,E,hE⟩ := normalized_power_count_all_primes_eventually_constant_of_ne_zero
    k p hk hp hk0 ha
  refine ⟨σ,?_⟩
  apply Tendsto.congr' _ tendsto_const_nhds
  exact eventually_atTop.mpr ⟨E,fun e he => (hE e he).symm⟩

#print axioms normalized_power_count_scaling_recurrence_all_primes
#print axioms normalized_power_count_all_primes_eventually_constant_of_ne_zero
#print axioms normalized_power_count_all_primes_tendsto_of_ne_zero
end WaringSiegel.WSL4Local
