import WaringSiegel.WSL2UnitBalancing
import Mathlib.Data.Int.Interval

/-!
# Counting actual units in a logarithmic box

The finite torsion factor and integer exponents come from mathlib's proved
Dirichlet unit theorem. Bounds on the logarithmic embedding bound these
integer exponents through the continuous inverse of its actual real basis.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem

namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]

/-- The actual torsion factor and fundamental-unit exponents of a unit. -/
def unitData (u : (𝓞 K)ˣ) : torsion K × (Fin (rank K) → ℤ) :=
  Classical.choose (exist_unique_eq_mul_prod K u)

theorem unitData_spec (u : (𝓞 K)ˣ) :
    u = (unitData u).1 * ∏ i, fundSystem K i ^ (unitData u).2 i :=
  (Classical.choose_spec (exist_unique_eq_mul_prod K u)).1

theorem unitData_injective : Function.Injective (unitData (K := K)) := by
  intro u v h
  rw [unitData_spec u, unitData_spec v, h]

theorem unitData_exponent_eq_repr (u : (𝓞 K)ˣ) (i : Fin (rank K)) :
    (((unitData u).2 i : ℤ) : ℝ) =
      ((basisUnitLattice K).ofZLatticeBasis ℝ).equivFun
        (logEmbedding K (Additive.ofMul u)) i := by
  let q : Additive ((𝓞 K)ˣ ⧸ torsion K) := Additive.ofMul (u : (𝓞 K)ˣ ⧸ torsion K)
  have hdata := fun_eq_repr K (unitData u).1.property (unitData_spec u)
  rw [Module.Basis.equivFun_apply]
  have hh := Module.Basis.ofZLatticeBasis_repr_apply ℝ (unitLattice K) (basisUnitLattice K)
    (logEmbeddingEquiv K q) i
  simp only [basisUnitLattice, Module.Basis.map_repr, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply] at hh
  have hcoe : (logEmbeddingEquiv K q : logSpace K) = logEmbedding K (Additive.ofMul u) :=
    logEmbeddingEquiv_apply K u
  rw [hcoe] at hh
  rw [basisUnitLattice, hh]
  congr 1
  exact congrFun hdata i

/-- Uniform comparison between integer exponents and logarithmic coordinates. -/
theorem exists_unit_exponent_constant (K : Type*) [Field K] [NumberField K] :
    ∃ A : ℝ, 0 < A ∧ ∀ u : (𝓞 K)ˣ, ∀ i : Fin (rank K),
      |((unitData u).2 i : ℝ)| ≤ A * ‖logEmbedding K (Additive.ofMul u)‖ := by
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ
  let f := B.equivFunL.toContinuousLinearMap
  refine ⟨‖f‖ + 1, by positivity, ?_⟩
  intro u i
  rw [unitData_exponent_eq_repr]
  change ‖f (logEmbedding K (Additive.ofMul u)) i‖ ≤ _
  calc
    _ ≤ ‖f (logEmbedding K (Additive.ofMul u))‖ := norm_le_pi_norm _ _
    _ ≤ ‖f‖ * ‖logEmbedding K (Additive.ofMul u)‖ := f.le_opNorm _
    _ ≤ (‖f‖ + 1) * ‖logEmbedding K (Additive.ofMul u)‖ := by
      nlinarith [norm_nonneg (logEmbedding K (Additive.ofMul u))]

/-- The finite integer exponent box used in the actual unit count. -/
def unitExponentBox (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finset (Fin (rank K) → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(n : ℤ)) (n : ℤ))

theorem unitExponentBox_card (n : ℕ) :
    (unitExponentBox K n).card = (2 * n + 1) ^ rank K := by
  have hi : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    have he : (n : ℤ) + 1 - -(n : ℤ) = ((2 * n + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [he, Int.toNat_natCast]
  simp only [unitExponentBox, Fintype.card_piFinset, hi, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- Finite torsion times the exact integer-coordinate box bounds any unit set. -/
theorem unit_finset_card_le_box (T : Finset (𝓞 K)ˣ) (n : ℕ)
    (hT : ∀ u ∈ T, ∀ i, |((unitData u).2 i : ℝ)| ≤ n) :
    T.card ≤ torsionOrder K * (2 * n + 1) ^ rank K := by
  have hsub : T.image unitData ⊆ (Finset.univ : Finset (torsion K)).product
      (unitExponentBox K n) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp (hT u hu i)
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  calc
    T.card = (T.image unitData).card := (Finset.card_image_of_injective _ unitData_injective).symm
    _ ≤ ((Finset.univ : Finset (torsion K)).product (unitExponentBox K n)).card :=
      Finset.card_le_card hsub
    _ = torsionOrder K * (2 * n + 1) ^ rank K := by
      rw [Finset.product_eq_sprod, Finset.card_product, Finset.card_univ, unitExponentBox_card]
      rfl

/-- Polynomial growth of actual units in bounded logarithmic coordinates,
with degree exactly the Dirichlet unit rank. -/
theorem exists_unit_log_count_constant (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 ≤ R → ∀ T : Finset (𝓞 K)ˣ,
      (∀ u ∈ T, ‖logEmbedding K (Additive.ofMul u)‖ ≤ R) →
      (T.card : ℝ) ≤ C * (1 + R) ^ rank K := by
  obtain ⟨A, hA, hexp⟩ := exists_unit_exponent_constant K
  refine ⟨(torsionOrder K : ℝ) * (2 * A + 3) ^ rank K, ?_, ?_⟩
  · exact mul_pos (by exact_mod_cast torsionOrder_pos K) (pow_pos (by linarith) _)
  · intro R hR T hT
    let n : ℕ := ⌈A * R⌉₊
    have hn : A * R ≤ (n : ℝ) := Nat.le_ceil _
    have hcard : T.card ≤ torsionOrder K * (2 * n + 1) ^ rank K := by
      apply unit_finset_card_le_box
      intro u hu i
      exact (hexp u i).trans ((mul_le_mul_of_nonneg_left (hT u hu) hA.le).trans hn)
    have hnhi : (n : ℝ) < A * R + 1 := Nat.ceil_lt_add_one (mul_nonneg hA.le hR)
    have hbase : ((2 * n + 1 : ℕ) : ℝ) ≤ (2 * A + 3) * (1 + R) := by
      push_cast
      nlinarith
    have hpow : (((2 * n + 1 : ℕ) : ℝ)) ^ rank K ≤
        ((2 * A + 3) * (1 + R)) ^ rank K :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    calc
      (T.card : ℝ) ≤ (torsionOrder K : ℝ) * (((2 * n + 1 : ℕ) : ℝ)) ^ rank K := by
        exact_mod_cast hcard
      _ ≤ (torsionOrder K : ℝ) * ((2 * A + 3) * (1 + R)) ^ rank K :=
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)
      _ = ((torsionOrder K : ℝ) * (2 * A + 3) ^ rank K) * (1 + R) ^ rank K := by
        rw [mul_pow]
        ring

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_unit_exponent_constant
#print axioms WaringSiegel.WSL2.exists_unit_log_count_constant
