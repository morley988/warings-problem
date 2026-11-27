import WaringSiegel.WSL4WeilDVRGood
import WaringSiegel.WSL3MomentLocalPowerPrimitiveAll

/-! # Uniform ramified bounds for single unit power roots -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing WSL3

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]
attribute [local instance] quotientFintype residueFintype

theorem one_power_branch_seed_card_le (k : ℕ) :
    Nat.card (PrimitivePowerBranchSeeds k R 1 1) ≤
      Nat.card (ResidueField R)^(powerDerivativeOrder R k+1) := by
  have h := Nat.card_le_card_of_injective
    (f:=fun α : PrimitivePowerBranchSeeds k R 1 1 => α.val) Subtype.val_injective
  simpa only [Nat.card_fun,Nat.card_fin,pow_one,dvr_power_quotient_card] using h

theorem local_single_power_count_uniform_bound
    (k : ℕ) (hk : 0<k) (hk0 : (k:R)≠0) (e : ℕ) :
    localPowerSolutionCount R (maximalIdeal R^e) k 1 1 ≤
      Nat.card (ResidueField R)^powerLocalPrecision R k := by
  by_cases he : powerLocalPrecision R k≤e
  · have he0 : e≠0 := by have := powerLocalPrecision_pos R k; omega
    have hr : e=(powerDerivativeOrder R k+1+(e-powerLocalPrecision R k))+
        powerDerivativeOrder R k := by
      dsimp [powerDerivativeOrder,powerLocalPrecision] at *
      omega
    have hc : localPowerSolutionCount R (maximalIdeal R^e) k 1 1=
        primitiveLocalPowerSolutionCount k R (maximalIdeal R^e)
          (Ideal.pow_le_self he0) 1 1 := by
      unfold localPowerSolutionCount primitiveLocalPowerSolutionCount
      exact Nat.card_congr (unitTargetPrimitivePowerSolutionsEquiv k hk _ _ _ isUnit_one)
    rw [hc,primitive_local_power_count_ramified_at k hk hk0 0 (e-powerLocalPrecision R k) e hr]
    simp only [zero_mul,zero_add]
    calc
      _ ≤ Nat.card (ResidueField R)^(powerDerivativeOrder R k+1)*
          Nat.card (ResidueField R)^powerDerivativeOrder R k :=
        Nat.mul_le_mul_right _ (one_power_branch_seed_card_le k)
      _ = _ := by
        rw [← pow_add]
        congr 1
        dsimp [powerDerivativeOrder,powerLocalPrecision]
        omega
  · have hc : localPowerSolutionCount R (maximalIdeal R^e) k 1 1 ≤
        Nat.card (R ⧸ maximalIdeal R^e) := by
      have h := Nat.card_le_card_of_injective
        (f:=fun x : LocalPowerSolutions R (maximalIdeal R^e) k 1 1 => x.val) Subtype.val_injective
      simpa only [Nat.card_fun,Nat.card_fin,pow_one] using h
    apply hc.trans
    rw [dvr_power_quotient_card]
    exact Nat.pow_le_pow_right Nat.card_pos (by omega)

theorem square_roots_count_bound_of_unit_root
    (h2 : (2:R)≠0) (n : ℕ) {z : R ⧸ maximalIdeal R^n} (hz : IsUnit z) :
    (Finset.univ.filter (fun x : R ⧸ maximalIdeal R^n => x^2=z^2)).card ≤
      Nat.card (ResidueField R)^powerLocalPrecision R 2 := by
  let iz : R ⧸ maximalIdeal R^n := ↑(hz.unit⁻¹)
  have hzi : z*iz=1 := by simpa only [iz,hz.unit_spec] using Units.mul_inv hz.unit
  let f : {x : R ⧸ maximalIdeal R^n // x^2=z^2} →
      LocalPowerSolutions R (maximalIdeal R^n) 2 1 1 := fun x =>
    ⟨fun _ => x.val*iz,by
      simp only [Fin.sum_univ_one,map_one]
      rw [mul_pow,x.property,← mul_pow,hzi,one_pow]⟩
  have hi : Function.Injective f := by
    intro x y h
    have hh := congrFun (congrArg Subtype.val h) (0 : Fin 1)
    change x.val*iz=y.val*iz at hh
    apply Subtype.ext
    exact (hz.unit⁻¹).isUnit.mul_right_cancel hh
  have hc := Nat.card_le_card_of_injective f hi
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at hc
  exact hc.trans (local_single_power_count_uniform_bound 2 (by decide) h2 n)

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.local_single_power_count_uniform_bound
#print axioms WaringSiegel.WSL4Weil.square_roots_count_bound_of_unit_root
