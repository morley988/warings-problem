import WaringSiegel.WSL4LocalPowerDensities

/-! # Recurrences and residue comparison for actual local power densities -/
noncomputable section
set_option maxHeartbeats 1400000
open IsLocalRing Filter Topology
open scoped BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem primitivePowerDensityAllPrimes_eq_residue
    (k s : ℕ) (hk : 0<k) (hku : IsUnit (k:R)) (a : R) :
    primitivePowerDensityAllPrimes R k (s+2) a=
      (Nat.card (PrimitivePowerResidues k R (s+2) a):ℝ)/
        (Nat.card (ResidueField R):ℝ)^(s+1) := by
  have h := normalized_primitive_local_power_count_ramified_eq
    k hk hku.ne_zero s (2*powerDerivativeOrder R k) le_rfl a
  rw [normalized_primitive_local_power_count_eq k hk hku (s+1)] at h
  exact h.symm

theorem localPowerDensity_eq_primitive_of_not_mem
    (k s : ℕ) (hk0 : ((k+1 : ℕ):R)≠0)
    {a : R} (ha : a ∉ maximalIdeal R^(k+1)) :
    localPowerDensity R (k+1) (s+2) a=
      primitivePowerDensityAllPrimes R (k+1) (s+2) a := by
  have ha0 : a≠0 := by intro h; exact ha (h ▸ (maximalIdeal R^(k+1)).zero_mem)
  apply tendsto_nhds_unique (tendsto_localPowerDensity_of_ne_zero
    (k+1) (s+2) (by omega) (by omega) hk0 ha0)
  apply Tendsto.congr' _ tendsto_const_nhds
  apply eventually_atTop.mpr
  refine ⟨2*powerDerivativeOrder R (k+1)+(k+1),fun e he => ?_⟩
  have heq : e=(e-(k+1))+k+1 := by omega
  rw [heq]
  exact (normalized_power_count_eq_of_not_mem_power_ideal
    k s (e-(k+1)) hk0 (by omega) ha).symm

theorem localPowerDensity_scaling_recurrence
    (k s : ℕ) (hk0 : ((k+1 : ℕ):R)≠0)
    {π : R} (hπ : Irreducible π) {b : R} (hb : b≠0) :
    localPowerDensity R (k+1) (s+2) (π^(k+1)*b)=
      primitivePowerDensityAllPrimes R (k+1) (s+2) (π^(k+1)*b)+
        localPowerDensity R (k+1) (s+2) b *
          ((Nat.card (ResidueField R):ℝ)^((s+2)*k) /
            (Nat.card (ResidueField R):ℝ)^((s+1)*(k+1))) := by
  have ha : π^(k+1)*b≠0 := mul_ne_zero (pow_ne_zero _ hπ.ne_zero) hb
  have hl : Tendsto (fun n : ℕ =>
      normalizedLocalPowerCount R (k+1) (s+2) (n+k+1) (π^(k+1)*b)) atTop
      (𝓝 (localPowerDensity R (k+1) (s+2) (π^(k+1)*b))) := by
    simpa only [Nat.add_assoc] using
      (tendsto_localPowerDensity_of_ne_zero (k+1) (s+2)
        (by omega) (by omega) hk0 ha).comp (tendsto_add_atTop_nat (k+1))
  have hconst : Tendsto (fun _ : ℕ =>
      primitivePowerDensityAllPrimes R (k+1) (s+2) (π^(k+1)*b)) atTop
      (𝓝 (primitivePowerDensityAllPrimes R (k+1) (s+2) (π^(k+1)*b))) :=
    tendsto_const_nhds
  have hr := hconst.add
    ((tendsto_localPowerDensity_of_ne_zero (k+1) (s+2)
      (by omega) (by omega) hk0 hb).mul_const
        ((Nat.card (ResidueField R):ℝ)^((s+2)*k) /
          (Nat.card (ResidueField R):ℝ)^((s+1)*(k+1))))
  apply tendsto_nhds_unique hl
  apply hr.congr'
  apply eventually_atTop.mpr
  refine ⟨2*powerDerivativeOrder R (k+1),fun n hn => ?_⟩
  exact (normalized_power_count_scaling_recurrence_all_primes
    k s n hk0 hπ (by omega) b).symm

theorem power_density_scaling_ratio_eq (k s : ℕ) (hks : k≤s+1) :
    ((Nat.card (ResidueField R):ℝ)^((s+2)*k) /
      (Nat.card (ResidueField R):ℝ)^((s+1)*(k+1)))=
      1/(Nat.card (ResidueField R):ℝ)^(s+1-k) := by
  have hq : (Nat.card (ResidueField R):ℝ)≠0 := by exact_mod_cast Nat.card_pos.ne'
  have he : (s+1)*(k+1)=(s+2)*k+(s+1-k) := by
    have hs := Nat.sub_add_cancel hks
    nlinarith
  rw [he,pow_add,← div_div,div_self (pow_ne_zero _ hq)]

theorem residue_card_inverse_square_le_half :
    1/(Nat.card (ResidueField R):ℝ)^2≤(1/2:ℝ) := by
  letI := Fintype.ofFinite (ResidueField R)
  have hq2 : (2:ℝ)≤Nat.card (ResidueField R) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (show 2≤Fintype.card (ResidueField R) from Fintype.one_lt_card)
  have hqpow : (2:ℝ)≤(Nat.card (ResidueField R):ℝ)^2 := by nlinarith
  exact one_div_le_one_div_of_le (by norm_num) hqpow

theorem power_density_scaling_ratio_le_square (k s : ℕ) (hks : k+1≤s) :
    ((Nat.card (ResidueField R):ℝ)^((s+2)*k) /
      (Nat.card (ResidueField R):ℝ)^((s+1)*(k+1)))≤
      1/(Nat.card (ResidueField R):ℝ)^2 := by
  rw [power_density_scaling_ratio_eq k s (by omega)]
  have hq : (1:ℝ)≤Nat.card (ResidueField R) := by exact_mod_cast Nat.card_pos
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ hq (by omega))

theorem primitivePowerDensityAllPrimes_good_upper
    (k s : ℕ) (hk : 0<k) (hs : 4≤s) (hku : IsUnit (k:R)) (a : R) :
    primitivePowerDensityAllPrimes R k (s+2) a≤
      1+((k-1:ℕ):ℝ)^6/(Nat.card (ResidueField R):ℝ)^2 := by
  letI := Fintype.ofFinite (ResidueField R)
  rw [primitivePowerDensityAllPrimes_eq_residue k s hk hku]
  have herr := (abs_le.mp (finite_field_power_all_order_normalized_error
    k (s+2) hk (by omega) (residue R a))).2
  simp only [← Nat.card_eq_fintype_card] at herr
  let out : PrimitivePowerResidues k R (s+2) a →
      {x : Fin (s+2) → ResidueField R // (∑ i,x i^k)=residue R a} :=
    fun x => ⟨x.val,x.property.1⟩
  have hinj : Function.Injective out := by
    intro x y h
    exact Subtype.ext (congrArg
      (fun z : {x : Fin (s+2) → ResidueField R // (∑ i,x i^k)=residue R a} => z.val) h)
  have hc := Nat.card_le_card_of_injective out hinj
  have hcR : (Nat.card (PrimitivePowerResidues k R (s+2) a):ℝ)≤
      Nat.card {x : Fin (s+2) → ResidueField R // (∑ i,x i^k)=residue R a} := by
    exact_mod_cast hc
  have hdiv := div_le_div_of_nonneg_right hcR
    (show 0≤(Nat.card (ResidueField R):ℝ)^(s+1) by positivity)
  have he : s+2-1=s+1 := by omega
  rw [he] at herr
  linarith

#print axioms localPowerDensity_scaling_recurrence
#print axioms primitivePowerDensityAllPrimes_good_upper
end WaringSiegel.WSL4Local
