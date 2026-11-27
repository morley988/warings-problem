import WaringSiegel.WSL3LocalConductorSeries

/-! # WSL3: uniform initial bounds for local conductor variation -/
noncomputable section
set_option maxHeartbeats 800000
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [Finite (ResidueField R)]

/-- Dropping the equation bounds singular tuples by all tuples in the zero
residue fiber. The bound is literal finite-quotient counting. -/
theorem singular_local_cubic_count_upper (n s : ℕ) (a : R) :
    Nat.card (SingularLocalCubicSolutions R (maximalIdeal R^(n+1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) s a) ≤
        Nat.card (ResidueField R)^(s*n) := by
  letI := dvr_power_quotient_finite (R := R) (n+1)
  let Z := {z : R ⧸ maximalIdeal R^(n+1) //
    localResidueReduction _ (Ideal.pow_le_self (Nat.succ_ne_zero n)) z = 0}
  let f : SingularLocalCubicSolutions R (maximalIdeal R^(n+1))
      (Ideal.pow_le_self (Nat.succ_ne_zero n)) s a → (Fin s → Z) :=
    fun x i => ⟨x.val i, x.property.2 i⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have h := Nat.card_le_card_of_injective f hf
  have hZ : Nat.card Z = Nat.card (ResidueField R)^n :=
    residue_reduction_fiber_card n 0
  simpa only [Nat.card_fun, Nat.card_fin, hZ, ← pow_mul, Nat.mul_comm n s] using h

theorem normalized_cubic_count_sub_primitive_bounds
    (h3 : IsUnit (3 : R)) (n : ℕ) (a : R) :
    0 ≤ normalizedLocalCubicCount R 8 (n+1) a - primitiveEightCubicDensity R a ∧
      normalizedLocalCubicCount R 8 (n+1) a - primitiveEightCubicDensity R a ≤
        (Nat.card (ResidueField R) : ℝ)^(8*n) /
          (Nat.card (ResidueField R) : ℝ)^(7*(n+1)) := by
  letI := dvr_power_quotient_finite (R := R) (n+1)
  have hc := local_cubic_count_primitive_add_singular (maximalIdeal R^(n+1))
    (Ideal.pow_le_self (Nat.succ_ne_zero n)) 8 a
  have hp := normalized_primitive_local_cubic_count_eq h3 7 n a
  change normalizedPrimitiveLocalCubicCount R 8 n a = primitiveEightCubicDensity R a at hp
  rw [← hp]
  unfold normalizedLocalCubicCount normalizedPrimitiveLocalCubicCount
  rw [hc]
  simp only [Nat.cast_add, add_div, add_sub_cancel_left]
  constructor
  · positivity
  · apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast singular_local_cubic_count_upper (R := R) n 8 a

theorem cubic_primitive_sharp_error_le_inv_cube :
    cubicPrimitiveSharpErrorBound R ≤ 257 / (Nat.card (ResidueField R) : ℝ)^3 := by
  have hq0 : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hq1 : 1 ≤ (Nat.card (ResidueField R) : ℝ) := le_of_lt residue_card_real_one_lt
  have h7 : 1 / (Nat.card (ResidueField R) : ℝ)^7 ≤
      1 / (Nat.card (ResidueField R) : ℝ)^3 :=
    one_div_le_one_div_of_le (pow_pos hq0 3) (pow_le_pow_right₀ hq1 (by decide))
  unfold cubicPrimitiveSharpErrorBound
  calc
    _ ≤ 256 / (Nat.card (ResidueField R) : ℝ)^3 +
        1 / (Nat.card (ResidueField R) : ℝ)^3 := add_le_add_left h7 _
    _ = _ := by ring

theorem normalized_cubic_count_initial_error
    (h6 : (6 : ResidueField R) ≠ 0) (n : ℕ) (hn : n ≤ 2) (a : R) :
    |normalizedLocalCubicCount R 8 (n+1) a - 1| ≤
      258 / (Nat.card (ResidueField R) : ℝ)^3 := by
  have hq0 : 0 < (Nat.card (ResidueField R) : ℝ) := by exact_mod_cast Nat.card_pos
  have hq1 : 1 ≤ (Nat.card (ResidueField R) : ℝ) := le_of_lt residue_card_real_one_lt
  obtain ⟨h0, hu⟩ := normalized_cubic_count_sub_primitive_bounds
    (three_isUnit_of_six_residue_ne_zero h6) n a
  have hr : (Nat.card (ResidueField R) : ℝ)^(8*n) /
        (Nat.card (ResidueField R) : ℝ)^(7*(n+1)) ≤
      1 / (Nat.card (ResidueField R) : ℝ)^3 := by
    apply (div_le_div_iff₀ (pow_pos hq0 _) (pow_pos hq0 3)).mpr
    rw [one_mul, ← pow_add]
    exact pow_le_pow_right₀ hq1 (by omega)
  obtain ⟨-, hpl, hpu⟩ := primitive_eight_density_bounds_sharp h6 a
  have hp : |primitiveEightCubicDensity R a - 1| ≤ cubicPrimitiveSharpErrorBound R := by
    apply abs_le.mpr
    constructor <;> linarith
  calc
    _ ≤ |normalizedLocalCubicCount R 8 (n+1) a - primitiveEightCubicDensity R a| +
        |primitiveEightCubicDensity R a - 1| := abs_sub_le _ _ _
    _ ≤ 1 / (Nat.card (ResidueField R) : ℝ)^3 +
        257 / (Nat.card (ResidueField R) : ℝ)^3 :=
      add_le_add (by rw [abs_of_nonneg h0]; exact hu.trans hr)
        (hp.trans cubic_primitive_sharp_error_le_inv_cube)
    _ = _ := by ring

end WaringSiegel
