import WaringSiegel.WSL3MomentLocalPowerStability
import WaringSiegel.WSL2LocalRamified

/-! # Exact derivative precision for kth powers on ramified unit branches -/
noncomputable section
set_option maxHeartbeats 1200000
open IsLocalRing
open scoped BigOperators
namespace WaringSiegel.WSL3

def powerBranchIdeal (R : Type*) [CommRing R] [IsLocalRing R] (k : ℕ) : Ideal R :=
  Ideal.span ({(k:R)} : Set R)*maximalIdeal R

theorem power_geometric_factor_of_branch
    {R : Type*} [CommRing R] [IsLocalRing R] (k : ℕ) {x y : R}
    (hy : y-x∈powerBranchIdeal R k) :
    ∃ c : R,c∈maximalIdeal R ∧
      (∑ j∈Finset.range k,y^j*x^(k-1-j))=(k:R)*(x^(k-1)+c) := by
  let J := powerBranchIdeal R k
  have hterm (j : ℕ) (hj : j∈Finset.range k) : y^j*x^(k-1-j)-x^(k-1)∈J := by
    have hjk := Finset.mem_range.mp hj
    have hp : x^(k-1)=x^j*x^(k-1-j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp,← sub_mul]
    apply J.mul_mem_right
    obtain ⟨u,hu⟩ := sub_dvd_pow_sub_pow y x j
    rw [hu]
    exact J.mul_mem_right u hy
  have hdiff : (∑ j∈Finset.range k,y^j*x^(k-1-j))-(k:R)*x^(k-1)∈J := by
    have hc : (k:R)*x^(k-1)=∑ _j∈Finset.range k,x^(k-1) := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    rw [hc,← Finset.sum_sub_distrib]
    exact Ideal.sum_mem J hterm
  obtain ⟨c,hc,hcd⟩ := Ideal.mem_span_singleton_mul.mp hdiff
  refine ⟨c,hc,?_⟩
  linear_combination -hcd

theorem power_sub_mem_nat_mul_iff_of_branch
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    (k : ℕ) (hk : (k:R)≠0) {x y : R} (hx : IsUnit x)
    (hy : y-x∈powerBranchIdeal R k) (I : Ideal R) :
    y^k-x^k∈Ideal.span ({(k:R)} : Set R)*I ↔ y-x∈I := by
  obtain ⟨c,hc,hfactor⟩ := power_geometric_factor_of_branch k hy
  let B : R := x^(k-1)+c
  have hB : IsUnit B := by
    apply (residue_ne_zero_iff_isUnit _).mp
    have hc0 := (residue_eq_zero_iff c).mpr hc
    simpa only [B,map_add,map_pow,hc0,add_zero] using
      pow_ne_zero (k-1) ((residue_ne_zero_iff_isUnit _).mpr hx)
  have he : y^k-x^k=(k:R)*(B*(y-x)) := by
    rw [← geom_sum₂_mul y x k,hfactor]
    ring
  rw [he,Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨d,hd,he⟩
    have hd' : d=B*(y-x) := mul_left_cancel₀ hk he
    rw [hd'] at hd
    exact (I.unit_mul_mem_iff_mem hB).mp hd
  · intro h
    exact ⟨B*(y-x),(I.unit_mul_mem_iff_mem hB).mpr h,rfl⟩

def powerDerivativeOrder (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (k : ℕ) : ℕ :=
  (IsDiscreteValuationRing.addVal R (k:R)).toNat

theorem span_nat_eq_maximalIdeal_pow
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k : ℕ) (hk : (k:R)≠0) :
    Ideal.span ({(k:R)} : Set R)=maximalIdeal R^powerDerivativeOrder R k := by
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨τ,u,hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hk hπ
  have hv : IsDiscreteValuationRing.addVal R (k:R)=τ :=
    IsDiscreteValuationRing.addVal_def _ u hπ τ hu
  simp only [powerDerivativeOrder,hv,ENat.toNat_coe]
  rw [hu,Ideal.span_singleton_mul_left_unit u.isUnit,hπ.maximalIdeal_eq,Ideal.span_singleton_pow]

theorem powerBranchIdeal_eq_power
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k : ℕ) (hk : (k:R)≠0) :
    powerBranchIdeal R k=maximalIdeal R^(powerDerivativeOrder R k+1) := by
  rw [powerBranchIdeal,span_nat_eq_maximalIdeal_pow R k hk,pow_succ]

theorem unit_power_congruence_precision
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k : ℕ) (hk : (k:R)≠0) {x y : R} (hx : IsUnit x)
    (hy : y-x∈maximalIdeal R^(powerDerivativeOrder R k+1)) (n : ℕ) :
    y^k-x^k∈maximalIdeal R^(n+powerDerivativeOrder R k) ↔ y-x∈maximalIdeal R^n := by
  have h := power_sub_mem_nat_mul_iff_of_branch k hk hx
    ((powerBranchIdeal_eq_power R k hk).symm ▸ hy) (maximalIdeal R^n)
  rwa [span_nat_eq_maximalIdeal_pow R k hk,← pow_add,Nat.add_comm] at h

def PowerRootBranch
    (R : Type*) [CommRing R] [IsLocalRing R] (k e L : ℕ) (hLe : L≤e) (a x : R) :=
  {z : R ⧸ maximalIdeal R^e // z^k=Ideal.Quotient.mk _ a ∧
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hLe) z=Ideal.Quotient.mk (maximalIdeal R^L) x}

theorem power_root_branch_card_of_root
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Finite (ResidueField R)] (k : ℕ) (hk : (k:R)≠0) {x : R} (hx : IsUnit x)
    (n : ℕ) (hn : powerDerivativeOrder R k+1≤n) :
    Nat.card (PowerRootBranch R k (n+powerDerivativeOrder R k)
      (powerDerivativeOrder R k+1) (by omega) (x^k) x)=
      Nat.card (ResidueField R)^powerDerivativeOrder R k := by
  let f := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I := maximalIdeal R) (Nat.le_add_right n (powerDerivativeOrder R k)))
  have he (z : R ⧸ maximalIdeal R^(n+powerDerivativeOrder R k)) :
      (z^k=Ideal.Quotient.mk _ (x^k) ∧
        Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega :
          powerDerivativeOrder R k+1≤n+powerDerivativeOrder R k)) z=
          Ideal.Quotient.mk (maximalIdeal R^(powerDerivativeOrder R k+1)) x) ↔
      f z=Ideal.Quotient.mk (maximalIdeal R^n) x := by
    obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective z
    simp only [f,Ideal.Quotient.factor_mk,← map_pow,Ideal.Quotient.eq]
    constructor
    · rintro ⟨hc,hb⟩
      exact (unit_power_congruence_precision k hk hx hb n).mp hc
    · intro hc
      have hb : y-x∈maximalIdeal R^(powerDerivativeOrder R k+1) := Ideal.pow_le_pow_right hn hc
      exact ⟨(unit_power_congruence_precision k hk hx hb n).mpr hc,hb⟩
  unfold PowerRootBranch
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact dvr_reduction_fiber_card n (powerDerivativeOrder R k) _

#print axioms unit_power_congruence_precision
#print axioms power_root_branch_card_of_root
end WaringSiegel.WSL3
