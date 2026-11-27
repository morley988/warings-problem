import WaringSiegel.WSL3MomentLocalPowerRamifiedLift

/-! # The uniform k-squared stability ideal, including primes dividing k -/
noncomputable section
set_option maxHeartbeats 1000000
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3

def powerStabilityIdeal (R : Type*) [CommRing R] [IsLocalRing R] (k : ℕ) : Ideal R :=
  Ideal.span ({(k:R)^2} : Set R)*maximalIdeal R

theorem unit_power_square_maximalIdeal_perturbation
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (k : ℕ) (hk : 0<k) {x c : R} (hx : IsUnit x) (hc : c∈maximalIdeal R) :
    ∃ y : R,y^k=x^k+(k:R)^2*c ∧ residue R y=residue R x ∧ IsUnit y := by
  let d : R := c*↑(hx.unit^k)⁻¹
  have hd : d∈maximalIdeal R := (maximalIdeal R).mul_mem_right _ hc
  have hinv : x^k*↑(hx.unit^k)⁻¹=1 := by
    simpa only [Units.val_pow_eq_pow_val,hx.unit_spec] using Units.mul_inv (hx.unit^k)
  have hxd : x^k*d=c := by
    calc
      x^k*d=c*(x^k*↑(hx.unit^k)⁻¹) := by dsimp [d]; ring
      _=c := by rw [hinv,mul_one]
  obtain ⟨z,hz,hzr,hzu⟩ := one_power_square_maximalIdeal_perturbation k hk hd
  refine ⟨x*z,?_,by rw [map_mul,hzr,mul_one],hx.mul hzu⟩
  calc
    (x*z)^k=x^k*(1+(k:R)^2*d) := by rw [mul_pow,hz]
    _=x^k+(k:R)^2*(x^k*d) := by ring
    _=_ := by rw [hxd]

theorem power_sum_adjust_free_coordinates_ramified
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (k : ℕ) (hk : 0<k) {s : ℕ}
    (x : Fin (s+1) → R) (hx : IsUnit (x 0)) (y : Fin s → R)
    (hy : ∀ i,y i-x i.succ∈powerStabilityIdeal R k) :
    ∃ z : R,z^k+∑ i,y i^k=∑ i,x i^k ∧ IsUnit z := by
  let d : R := ∑ i,(x i.succ^k-y i^k)
  have hd : d∈powerStabilityIdeal R k := by
    apply Ideal.sum_mem
    intro i _
    have hi : x i.succ-y i∈powerStabilityIdeal R k := by
      simpa only [neg_sub] using (powerStabilityIdeal R k).neg_mem (hy i)
    obtain ⟨u,hu⟩ := sub_dvd_pow_sub_pow (x i.succ) (y i) k
    rw [hu]
    exact (powerStabilityIdeal R k).mul_mem_right _ hi
  obtain ⟨c,hc,hcd⟩ := Ideal.mem_span_singleton_mul.mp hd
  obtain ⟨z,hz,-,hzu⟩ := unit_power_square_maximalIdeal_perturbation k hk hx hc
  refine ⟨z,?_,hzu⟩
  rw [hz,hcd,Fin.sum_univ_succ]
  simp only [d,Finset.sum_sub_distrib]
  abel

def powerLocalPrecision (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (k : ℕ) : ℕ :=
  2*(IsDiscreteValuationRing.addVal R (k:R)).toNat+1

theorem powerLocalPrecision_pos
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (k : ℕ) :
    0<powerLocalPrecision R k := Nat.zero_lt_succ _

theorem power_stability_ideal_eq_power
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k : ℕ) (hk : (k:R)≠0) :
    maximalIdeal R^powerLocalPrecision R k=powerStabilityIdeal R k := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨τ,u,hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hk hπ
  have hv : IsDiscreteValuationRing.addVal R (k:R)=τ :=
    IsDiscreteValuationRing.addVal_def _ u hπ τ hu
  have hsq : (k:R)^2=(↑(u^2):R)*π^(2*τ) := by
    rw [hu]
    simp only [Units.val_pow_eq_pow_val,mul_pow,Nat.mul_comm 2 τ,pow_mul]
  have hspan : Ideal.span ({(k:R)^2} : Set R)=maximalIdeal R^(2*τ) := by
    rw [hsq,Ideal.span_singleton_mul_left_unit (u^2).isUnit,
      hπ.maximalIdeal_eq,Ideal.span_singleton_pow]
  unfold powerLocalPrecision powerStabilityIdeal
  rw [hv,ENat.toNat_coe,hspan,pow_succ]

#print axioms unit_power_square_maximalIdeal_perturbation
#print axioms power_sum_adjust_free_coordinates_ramified
#print axioms power_stability_ideal_eq_power
end WaringSiegel.WSL3
