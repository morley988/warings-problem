import WaringSiegel.WSL4LocalPowerDensityRecurrence

/-! # Target-uniform upper bounds for actual good-prime power densities -/
noncomputable section
set_option maxHeartbeats 1800000
open IsLocalRing Filter Topology
open scoped BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

theorem localPowerDensity_good_coarse_unit_pow
    (k s : ℕ) (hs : 4≤s) (hks : k+1≤s) (hku : IsUnit ((k+1:ℕ):R))
    {π : R} (hπ : Irreducible π) (u : Rˣ) (t : ℕ) :
    localPowerDensity R (k+1) (s+2) ((u:R)*π^t)≤
      2*(1+(k:ℝ)^6/(Nat.card (ResidueField R):ℝ)^2) := by
  let A : ℝ := 1+(k:ℝ)^6/(Nat.card (ResidueField R):ℝ)^2
  let r : ℝ := (Nat.card (ResidueField R):ℝ)^((s+2)*k) /
    (Nat.card (ResidueField R):ℝ)^((s+1)*(k+1))
  have hA : 0≤A := by dsimp [A]; positivity
  have hr : 0≤r := by dsimp [r]; positivity
  have hrhalf : r≤(1/2:ℝ) :=
    (power_density_scaling_ratio_le_square k s hks).trans
      (residue_card_inverse_square_le_half (R:=R))
  have hprim (a : R) : primitivePowerDensityAllPrimes R (k+1) (s+2) a≤A := by
    simpa only [Nat.add_sub_cancel] using
      primitivePowerDensityAllPrimes_good_upper (k+1) s (by omega) hs hku a
  change localPowerDensity R (k+1) (s+2) ((u:R)*π^t)≤2*A
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases ht : t<k+1
    · rw [localPowerDensity_eq_primitive_of_not_mem k s hku.ne_zero
        (unit_mul_uniformizer_pow_not_mem_power_ideal hπ u ht)]
      exact (hprim _).trans (by linarith)
    · have hkt : k+1≤t := by omega
      have hsmall := ih (t-(k+1)) (by omega)
      have ha : (u:R)*π^t=π^(k+1)*((u:R)*π^(t-(k+1))) := by
        calc
          (u:R)*π^t=(u:R)*(π^(t-(k+1))*π^(k+1)) := by
            rw [← pow_add,Nat.sub_add_cancel hkt]
          _=π^(k+1)*((u:R)*π^(t-(k+1))) := by ring
      have hb : (u:R)*π^(t-(k+1))≠0 :=
        mul_ne_zero u.isUnit.ne_zero (pow_ne_zero _ hπ.ne_zero)
      rw [ha,localPowerDensity_scaling_recurrence k s hku.ne_zero hπ hb]
      change primitivePowerDensityAllPrimes R (k+1) (s+2)
          (π^(k+1)*((u:R)*π^(t-(k+1)))) +
        localPowerDensity R (k+1) (s+2) ((u:R)*π^(t-(k+1)))*r≤2*A
      have hm := mul_le_mul_of_nonneg_right hsmall hr
      have hc := mul_le_mul_of_nonneg_left hrhalf (show 0≤2*A by positivity)
      have hp := hprim (π^(k+1)*((u:R)*π^(t-(k+1))))
      nlinarith

theorem localPowerDensity_good_coarse
    (k s : ℕ) (hs : 4≤s) (hks : k+1≤s) (hku : IsUnit ((k+1:ℕ):R))
    {a : R} (ha : a≠0) :
    localPowerDensity R (k+1) (s+2) a≤
      2*(1+(k:ℝ)^6/(Nat.card (ResidueField R):ℝ)^2) := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨t,u,rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  exact localPowerDensity_good_coarse_unit_pow k s hs hks hku hπ u t

theorem localPowerDensity_good_upper_error
    (k s : ℕ) (hs : 4≤s) (hks : k+1≤s) (hku : IsUnit ((k+1:ℕ):R))
    {a : R} (ha0 : a≠0) :
    localPowerDensity R (k+1) (s+2) a-1≤
      2*((k:ℝ)^6+1)/(Nat.card (ResidueField R):ℝ)^2 := by
  let D : ℝ := (k:ℝ)^6/(Nat.card (ResidueField R):ℝ)^2
  let u : ℝ := 1/(Nat.card (ResidueField R):ℝ)^2
  have hD : 0≤D := by dsimp [D]; positivity
  have hu : 0≤u := by dsimp [u]; positivity
  have huhalf : u≤(1/2:ℝ) := residue_card_inverse_square_le_half (R:=R)
  have he : 2*((k:ℝ)^6+1)/(Nat.card (ResidueField R):ℝ)^2=2*D+2*u := by
    dsimp [D,u]
    ring
  rw [he]
  have hp (b : R) : primitivePowerDensityAllPrimes R (k+1) (s+2) b≤1+D := by
    simpa only [Nat.add_sub_cancel] using
      primitivePowerDensityAllPrimes_good_upper (k+1) s (by omega) hs hku b
  by_cases ha : a∈maximalIdeal R^(k+1)
  · obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    rw [hπ.maximalIdeal_eq,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at ha
    obtain ⟨b,rfl⟩ := ha
    have hb : b≠0 := (mul_ne_zero_iff.mp ha0).2
    rw [localPowerDensity_scaling_recurrence k s hku.ne_zero hπ hb]
    let r : ℝ := (Nat.card (ResidueField R):ℝ)^((s+2)*k) /
      (Nat.card (ResidueField R):ℝ)^((s+1)*(k+1))
    have hr : 0≤r := by dsimp [r]; positivity
    have hru : r≤u := power_density_scaling_ratio_le_square k s hks
    have hbnd : localPowerDensity R (k+1) (s+2) b≤2*(1+D) :=
      localPowerDensity_good_coarse k s hs hks hku hb
    have hm := mul_le_mul_of_nonneg_right hbnd hr
    have hmr := mul_le_mul_of_nonneg_left hru (show 0≤2*(1+D) by positivity)
    have hsmall := mul_le_mul_of_nonneg_right huhalf (show 0≤2*D by positivity)
    have hprim := hp (π^(k+1)*b)
    change primitivePowerDensityAllPrimes R (k+1) (s+2) (π^(k+1)*b)+
      localPowerDensity R (k+1) (s+2) b*r-1≤2*D+2*u
    nlinarith
  · rw [localPowerDensity_eq_primitive_of_not_mem k s hku.ne_zero ha]
    have h := hp a
    linarith

#print axioms localPowerDensity_good_coarse
#print axioms localPowerDensity_good_upper_error
end WaringSiegel.WSL4Local
