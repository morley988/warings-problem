import WaringSiegel.WSL4WeilQuadraticRoots
import WaringSiegel.WSL4PowerCharacterScaling

/-! # Actual prime-power stationary sums in a discrete valuation ring -/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical
open IsLocalRing

theorem finite_predicate_preimage_card
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (P : B → Prop) [DecidablePred P] (N : ℕ)
    (hN : ∀ y : B, Nat.card {x : A // f x=y}=N) :
    (Finset.univ.filter (fun x : A => P (f x))).card=
      (Finset.univ.filter P).card*N := by
  let e : {x : A // P (f x)} ≃
      (Σ y : {y : B // P y}, {x : A // f x=y.val}) :=
    { toFun := fun x => ⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
      invFun := fun y => ⟨y.2.val, by rw [y.2.property]; exact y.1.property⟩
      left_inv := fun _ => rfl
      right_inv := by rintro ⟨⟨y,hy⟩,⟨x,hx⟩⟩; cases hx; rfl }
  have he := Nat.card_congr e
  rw [Nat.card_sigma] at he
  simp only [hN, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card, Fintype.card_subtype] at he
  exact he

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Finite (ResidueField R)]

local instance quotientFintype (n : ℕ) : Fintype (R ⧸ maximalIdeal R^n) := by
  letI := dvr_power_quotient_finite (R:=R) n
  exact Fintype.ofFinite _
local instance residueFintype : Fintype (ResidueField R) := Fintype.ofFinite _

def dvrCubicSum (n : ℕ) (ψ : AddChar (R ⧸ maximalIdeal R^n) ℂ) (a b : R) : ℂ :=
  mixedCubicSum ψ (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b)

theorem uniformizer_power_quotient_square_zero
    {π : R} (hπ : Irreducible π) (n m : ℕ) (hnm : n≤m) :
    (Ideal.Quotient.mk (maximalIdeal R^(n+m)) (π^m))^2=0 := by
  rw [← map_pow, ← pow_mul, Ideal.Quotient.eq_zero_iff_mem,
    hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact pow_dvd_pow π (by omega)

theorem uniformizer_derivative_zero_iff
    {π : R} (hπ : Irreducible π) (n m : ℕ) (a b : R)
    (x : R ⧸ maximalIdeal R^(n+m)) :
    Ideal.Quotient.mk (maximalIdeal R^(n+m)) (π^m)*
        (3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b)=0 ↔
      3*Ideal.Quotient.mk (maximalIdeal R^n) a*
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n m)) x)^2+
          Ideal.Quotient.mk _ b=0 := by
  obtain ⟨y,rfl⟩ := Ideal.Quotient.mk_surjective x
  have he : Ideal.Quotient.mk (maximalIdeal R^(n+m)) (π^m)*
      (3*Ideal.Quotient.mk _ a*(Ideal.Quotient.mk _ y)^2+Ideal.Quotient.mk _ b)=
      Ideal.Quotient.mk (maximalIdeal R^(n+m)) (π^m*(3*a*y^2+b)) := by
    simp only [map_mul, map_add, map_pow, map_ofNat]
  rw [he, Ideal.Quotient.eq_zero_iff_mem, uniformizer_power_cancel_mem hπ m n]
  rw [Ideal.Quotient.factor_mk]
  have he' : 3*Ideal.Quotient.mk (maximalIdeal R^n) a*(Ideal.Quotient.mk _ y)^2+
      Ideal.Quotient.mk _ b=Ideal.Quotient.mk (maximalIdeal R^n) (3*a*y^2+b) := by
    simp only [map_mul, map_add, map_pow, map_ofNat]
  rw [he', Ideal.Quotient.eq_zero_iff_mem]

theorem dvrCubicSum_stationary_restriction
    {π : R} (hπ : Irreducible π) (n m : ℕ) (hnm : n≤m)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+m)) ℂ) (hψ : ψ.IsPrimitive) (a b : R) :
    dvrCubicSum (n+m) ψ a b =
      ∑ x ∈ Finset.univ.filter (fun x : R ⧸ maximalIdeal R^(n+m) =>
        3*Ideal.Quotient.mk (maximalIdeal R^n) a*
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_add_right n m)) x)^2+
            Ideal.Quotient.mk _ b=0),
        ψ (Ideal.Quotient.mk (maximalIdeal R^(n+m)) a*x^3+Ideal.Quotient.mk _ b*x) := by
  unfold dvrCubicSum
  rw [mixedCubicSum_stationary_restriction ψ hψ _ _
    (Ideal.Quotient.mk _ (π^m)) (uniformizer_power_quotient_square_zero hπ n m hnm)]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    uniformizer_derivative_zero_iff hπ n m a b]

theorem dvrCubicSum_norm_le_stationary_roots
    {π : R} (hπ : Irreducible π) (n m : ℕ) (hnm : n≤m)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+m)) ℂ) (hψ : ψ.IsPrimitive) (a b : R) :
    ‖dvrCubicSum (n+m) ψ a b‖ ≤ (Nat.card (ResidueField R) : ℝ)^m *
      (Finset.univ.filter (fun x : R ⧸ maximalIdeal R^n =>
        3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b=0)).card := by
  let f := Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (I:=maximalIdeal R) (Nat.le_add_right n m))
  let P : R ⧸ maximalIdeal R^n → Prop := fun x =>
    3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b=0
  have hc := finite_predicate_preimage_card f P (Nat.card (ResidueField R)^m)
    (fun y => dvr_reduction_fiber_card n m y)
  rw [dvrCubicSum_stationary_restriction hπ n m hnm ψ hψ a b]
  calc
    _ ≤ ((Finset.univ.filter (fun x => P (f x))).card : ℝ) := by
      exact (norm_sum_le _ _).trans_eq (by simp [P,f])
    _ = _ := by rw [hc]; push_cast; ring

theorem dvrCubicSum_norm_le_two_pow_of_unit_linear
    {π : R} (hπ : Irreducible π) (n m : ℕ) (hn : 1≤n) (hnm : n≤m)
    (ψ : AddChar (R ⧸ maximalIdeal R^(n+m)) ℂ) (hψ : ψ.IsPrimitive)
    (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R)) {a b : R} (ha : IsUnit a) (hb : IsUnit b) :
    ‖dvrCubicSum (n+m) ψ a b‖ ≤ 2*(Nat.card (ResidueField R) : ℝ)^m := by
  have hc := quadratic_unit_roots_card_le_two (maximalIdeal R^n)
    (Ideal.pow_le_self (by omega)) h2 (h3.mul ha) hb
  simp only [map_mul, map_ofNat] at hc
  have hcr : ((Finset.univ.filter (fun x : R ⧸ maximalIdeal R^n =>
      3*Ideal.Quotient.mk _ a*x^2+Ideal.Quotient.mk _ b=0)).card : ℝ) ≤ 2 := by
    exact_mod_cast hc
  apply (dvrCubicSum_norm_le_stationary_roots hπ n m hnm ψ hψ a b).trans
  exact (mul_le_mul_of_nonneg_left hcr (by positivity)).trans_eq (mul_comm _ _)

end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_norm_le_stationary_roots
#print axioms WaringSiegel.WSL4Weil.dvrCubicSum_norm_le_two_pow_of_unit_linear
