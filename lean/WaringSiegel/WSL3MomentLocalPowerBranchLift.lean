import WaringSiegel.WSL3MomentLocalPowerBranch

/-! # Exact kth-root branches for all targets in the ramified stability neighborhood -/
noncomputable section
set_option maxHeartbeats 1400000
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3

theorem one_power_branch_perturbation
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (k : ℕ) (hk : 0<k) {c : R} (hc : c∈maximalIdeal R) :
    ∃ t : R,t∈maximalIdeal R ∧ (1+(k:R)*t)^k=1+(k:R)^2*c := by
  obtain ⟨N,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  obtain ⟨t,htm,ht⟩ := unit_linear_correction_surjective N
    (fun j => ((N+1).choose (j+2):R)*(N+1:R)^j) hc
  refine ⟨t,htm,?_⟩
  rw [show (↑(N+1):R)=(N+1:R) by push_cast; rfl,unit_power_correction_identity,ht]

theorem unit_power_stability_branch
    {R : Type*} [CommRing R] [HenselianLocalRing R]
    (k : ℕ) (hk : 0<k) {x a : R} (hx : IsUnit x)
    (ha : a-x^k∈powerStabilityIdeal R k) :
    ∃ y : R,y^k=a ∧ y-x∈powerBranchIdeal R k := by
  obtain ⟨c,hc,he⟩ := Ideal.mem_span_singleton_mul.mp ha
  let d : R := c*↑(hx.unit^k)⁻¹
  have hd : d∈maximalIdeal R := (maximalIdeal R).mul_mem_right _ hc
  have hinv : x^k*↑(hx.unit^k)⁻¹=1 := by
    simpa only [Units.val_pow_eq_pow_val,hx.unit_spec] using Units.mul_inv (hx.unit^k)
  have hxd : x^k*d=c := by
    calc
      x^k*d=c*(x^k*↑(hx.unit^k)⁻¹) := by dsimp [d]; ring
      _=c := by rw [hinv,mul_one]
  obtain ⟨t,ht,hpower⟩ := one_power_branch_perturbation k hk hd
  refine ⟨x*(1+(k:R)*t),?_,?_⟩
  · have hdiff : (x*(1+(k:R)*t))^k-x^k=(k:R)^2*c := by
      rw [mul_pow,hpower]
      calc
        x^k*(1+(k:R)^2*d)-x^k=(k:R)^2*(x^k*d) := by ring
        _=_ := by rw [hxd]
    rw [he] at hdiff
    exact sub_left_inj.mp hdiff
  · apply Ideal.mem_span_singleton_mul.mpr
    exact ⟨x*t,(maximalIdeal R).mul_mem_left _ ht,by ring⟩

theorem power_sub_mem_stability_of_branch
    {R : Type*} [CommRing R] [IsLocalRing R] (k : ℕ) {x y : R}
    (hy : y-x∈powerBranchIdeal R k) : y^k-x^k∈powerStabilityIdeal R k := by
  obtain ⟨t,ht,he⟩ := Ideal.mem_span_singleton_mul.mp hy
  obtain ⟨c,hc,hfactor⟩ := power_geometric_factor_of_branch k hy
  have hid : y^k-x^k=(k:R)^2*((x^(k-1)+c)*t) := by
    rw [← geom_sum₂_mul y x k,hfactor,← he]
    ring
  rw [hid]
  exact Ideal.mem_span_singleton_mul.mpr
    ⟨(x^(k-1)+c)*t,(maximalIdeal R).mul_mem_left _ ht,rfl⟩

theorem power_root_branch_card
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k : ℕ) (hk : 0<k) (hk0 : (k:R)≠0) {x a : R} (hx : IsUnit x)
    (ha : a-x^k∈powerStabilityIdeal R k)
    (n : ℕ) (hn : powerDerivativeOrder R k+1≤n) :
    Nat.card (PowerRootBranch R k (n+powerDerivativeOrder R k)
      (powerDerivativeOrder R k+1) (by omega) a x)=
        Nat.card (ResidueField R)^powerDerivativeOrder R k := by
  obtain ⟨y,hy,hyx⟩ := unit_power_stability_branch k hk hx ha
  have hyx' : y-x∈maximalIdeal R^(powerDerivativeOrder R k+1) :=
    (powerBranchIdeal_eq_power R k hk0) ▸ hyx
  have hr : residue R y=residue R x := Ideal.Quotient.eq.mpr
    (Ideal.pow_le_self (Nat.succ_ne_zero _) hyx')
  have hyu : IsUnit y := (residue_ne_zero_iff_isUnit y).mp
    (hr ▸ (residue_ne_zero_iff_isUnit x).mpr hx)
  have hq : Ideal.Quotient.mk (maximalIdeal R^(powerDerivativeOrder R k+1)) y=
      Ideal.Quotient.mk _ x := Ideal.Quotient.eq.mpr hyx'
  have he : PowerRootBranch R k (n+powerDerivativeOrder R k)
      (powerDerivativeOrder R k+1) (by omega) a x=
      PowerRootBranch R k (n+powerDerivativeOrder R k)
        (powerDerivativeOrder R k+1) (by omega) (y^k) y := by
    unfold PowerRootBranch
    rw [hy,hq]
  rw [he]
  exact power_root_branch_card_of_root k hk0 hyu n hn

#print axioms unit_power_stability_branch
#print axioms power_root_branch_card
end WaringSiegel.WSL3
