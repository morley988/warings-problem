import WaringSiegel.WSL4WeilCriticalUnitRoots
import WaringSiegel.WSL2LocalModifiedDensity

/-! # Uniform stationary bounds for the unit part of a local cubic sum -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing WSL3

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]
attribute [local instance] quotientFintype residueFintype

def dvrUnitCubicSum (r : ℕ) (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ) (a b : R) : ℂ :=
  ∑ x ∈ Finset.univ.filter IsUnit,
    ψ (Ideal.Quotient.mk (maximalIdeal R^r) a*x^3+Ideal.Quotient.mk _ b*x)

theorem dvr_factor_isUnit_iff (n m : ℕ) (hn : 1≤n)
    (x : R ⧸ maximalIdeal R^(n+m)) :
    IsUnit (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (I:=maximalIdeal R) (Nat.le_add_right n m)) x) ↔ IsUnit x := by
  rw [← localResidueReduction_ne_zero_iff_isUnit (maximalIdeal R^n)
    (Ideal.pow_le_self (by omega)),
    ← localResidueReduction_ne_zero_iff_isUnit (maximalIdeal R^(n+m))
      (Ideal.pow_le_self (by omega))]
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Ideal.Quotient.factor_mk,localResidueReduction_mk]

theorem dvr_isUnit_translation_iff {π : R} (hπ : Irreducible π)
    (n m : ℕ) (hm : 1≤m) (x t : R ⧸ maximalIdeal R^(n+m)) :
    IsUnit (x+Ideal.Quotient.mk _ (π^m)*t) ↔ IsUnit x := by
  let ρ := localResidueReduction (maximalIdeal R^(n+m)) (Ideal.pow_le_self (by omega))
  have hc : ρ (Ideal.Quotient.mk _ (π^m))=0 := by
    rw [localResidueReduction_mk,map_pow]
    have hp : residue R π=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (by rw [hπ.maximalIdeal_eq]; exact Ideal.subset_span (by simp))
    rw [hp,zero_pow (by omega)]
  rw [← localResidueReduction_ne_zero_iff_isUnit _ (Ideal.pow_le_self (by omega)),
    ← localResidueReduction_ne_zero_iff_isUnit _ (Ideal.pow_le_self (by omega))]
  change ρ (x+Ideal.Quotient.mk _ (π^m)*t)≠0 ↔ ρ x≠0
  rw [map_add,map_mul,hc,zero_mul,add_zero]

theorem dvrUnitCubicSum_stationary_restriction
    {π : R} (hπ : Irreducible π) (n m : ℕ) (hn : 1≤n) (hnm : n≤m)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+m)) ℂ) (hψ : ψ.IsPrimitive) (a b : R) :
    dvrUnitCubicSum (n+m) ψ a b =
      ∑ x ∈ Finset.univ.filter (fun x : R ⧸ maximalIdeal R^(n+m) =>
        IsUnit x ∧ 3*Ideal.Quotient.mk (maximalIdeal R^n) a*
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n m)) x)^2+
            Ideal.Quotient.mk _ b=0),
        ψ (Ideal.Quotient.mk (maximalIdeal R^(n+m)) a*x^3+Ideal.Quotient.mk _ b*x) := by
  let w : R ⧸ maximalIdeal R^(n+m) → ℂ := fun x => if IsUnit x then 1 else 0
  have hw : ∀x t,w (x+Ideal.Quotient.mk _ (π^m)*t)=w x := by
    intro x t
    simp only [w,dvr_isUnit_translation_iff hπ n m (by omega)]
  have he := weighted_cubic_sum_stationary_restriction ψ hψ
    (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) (Ideal.Quotient.mk _ (π^m))
    (uniformizer_power_quotient_square_zero hπ n m hnm) w hw
  have hl : (∑x,w x*ψ (Ideal.Quotient.mk _ a*x^3+Ideal.Quotient.mk _ b*x))=
      dvrUnitCubicSum (n+m) ψ a b := by
    simp only [dvrUnitCubicSum,w,Finset.sum_filter,ite_mul,one_mul,zero_mul]
  rw [hl] at he
  apply he.trans
  simp only [Finset.sum_filter,w,ite_mul,one_mul,zero_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [uniformizer_derivative_zero_iff hπ n m a b]
  by_cases hu : IsUnit x <;> by_cases hd :
      3*Ideal.Quotient.mk (maximalIdeal R^n) a*
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n m)) x)^2+
          Ideal.Quotient.mk _ b=0 <;>
    simp only [hu,hd,and_true,and_false,true_and,false_and,if_true,if_false]

theorem dvrUnitCubicSum_norm_le_stationary_roots
    {π : R} (hπ : Irreducible π) (n m : ℕ) (hn : 1≤n) (hnm : n≤m)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+m)) ℂ) (hψ : ψ.IsPrimitive) (a b : R) :
    ‖dvrUnitCubicSum (n+m) ψ a b‖ ≤ (Nat.card (ResidueField R) : ℝ)^m *
      (Finset.univ.filter (fun x : R ⧸ maximalIdeal R^n =>
        IsUnit x ∧ 3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b=0)).card := by
  let f := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I:=maximalIdeal R) (Nat.le_add_right n m))
  let P : R ⧸ maximalIdeal R^n → Prop := fun x =>
    IsUnit x ∧ 3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b=0
  have hc := finite_predicate_preimage_card f P (Nat.card (ResidueField R)^m)
    (fun y => dvr_reduction_fiber_card n m y)
  rw [dvrUnitCubicSum_stationary_restriction hπ n m hn hnm ψ hψ a b]
  have he : Finset.univ.filter (fun x : R ⧸ maximalIdeal R^(n+m) =>
      IsUnit x ∧ 3*Ideal.Quotient.mk (maximalIdeal R^n) a*(f x)^2+Ideal.Quotient.mk _ b=0)=
        Finset.univ.filter (fun x => P (f x)) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,P,f,dvr_factor_isUnit_iff n m hn]
  change ‖∑x∈_,_‖≤_
  rw [he]
  calc
    _ ≤ ((Finset.univ.filter (fun x => P (f x))).card : ℝ) :=
      (norm_sum_le _ _).trans_eq (by simp)
    _ = _ := by rw [hc]; push_cast; ring

variable [HenselianLocalRing R]

def cubicUnitBoundConstant (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : ℝ :=
  (Nat.card (ResidueField R) : ℝ)^(powerDerivativeOrder R 3+powerLocalPrecision R 2+1)

theorem dvrUnitCubicSum_uniform_bound
    {π : R} (hπ : Irreducible π) (h2 : (2:R)≠0) (h3 : (3:R)≠0)
    (r : ℕ) (hr : 2≤r) (ψ : AddChar (R ⧸ maximalIdeal R^r) ℂ)
    (hψ : ψ.IsPrimitive) {a : R} (ha : IsUnit a) (b : R) :
    ‖dvrUnitCubicSum r ψ a b‖ ≤ cubicUnitBoundConstant R*
      (Nat.card (ResidueField R) : ℝ)^((r:ℝ)/2) := by
  let q : ℝ := Nat.card (ResidueField R)
  have hq : 1≤q := by
    dsimp [q]
    exact_mod_cast (show 1≤Nat.card (ResidueField R) from Nat.card_pos)
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  let n := r/2
  let m := r-r/2
  have hn : 1≤n := by dsimp [n]; omega
  have hnm : n≤m := by dsimp [n,m]; omega
  have he : n+m=r := by dsimp [n,m]; omega
  have hs := dvrUnitCubicSum_norm_le_stationary_roots hπ n m hn hnm
  rw [he] at hs
  have hbnd := hs ψ hψ a b
  have hcount := cubic_critical_unit_count_uniform h2 h3 n ha b
  have hcountR : ((Finset.univ.filter (fun x : R ⧸ maximalIdeal R^n =>
      IsUnit x ∧ 3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b=0)).card : ℝ) ≤
      q^(powerDerivativeOrder R 3+powerLocalPrecision R 2) := by
    dsimp [q]
    exact_mod_cast hcount
  apply hbnd.trans
  apply (mul_le_mul_of_nonneg_left hcountR (by positivity)).trans
  change q^m*q^(powerDerivativeOrder R 3+powerLocalPrecision R 2)≤_
  rw [← pow_add]
  have hm : (m:ℝ)≤(r:ℝ)/2+1 := by
    have hmn : 2*m≤r+2 := by dsimp [m]; omega
    have hreal : 2*(m:ℝ)≤r+2 := by exact_mod_cast hmn
    linarith
  rw [← Real.rpow_natCast]
  unfold cubicUnitBoundConstant
  change q^((m+(powerDerivativeOrder R 3+powerLocalPrecision R 2):ℕ):ℝ)≤
    q^(powerDerivativeOrder R 3+powerLocalPrecision R 2+1)*q^((r:ℝ)/2)
  rw [← Real.rpow_natCast,← Real.rpow_add hq0]
  apply Real.rpow_le_rpow_of_exponent_le hq
  push_cast
  linarith
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.dvrUnitCubicSum_uniform_bound
