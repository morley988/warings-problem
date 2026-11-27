import WaringSiegel.WSL2UnitTransport
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.FundamentalCone

/-!
# Genuine unit balancing at every infinite place

The proof uses mathlib's proved Dirichlet unit theorem and its actual unit
lattice. Rounding in a bounded fundamental domain, at scale 1/(2k), produces
the kth power of a square unit. Squaring guarantees total positivity without
postulating a full-rank lattice of positive units. Both upper and lower
archimedean bounds are uniform in the nonzero target.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem

namespace WaringSiegel.WSL2

variable {K : Type*} [Field K] [NumberField K]

/-- The actual logarithmic unit lattice has a bounded covering domain. -/
theorem exists_log_unit_covering_radius (K : Type*) [Field K] [NumberField K] :
    ∃ R : ℝ, 0 < R ∧ ∀ z : logSpace K, ∃ u : (𝓞 K)ˣ,
      ‖logEmbedding K (Additive.ofMul u) + z‖ ≤ R := by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ
  obtain ⟨R, hR, hbound⟩ := (ZSpan.fundamentalDomain_isBounded B).exists_pos_norm_le
  refine ⟨R, hR, ?_⟩
  intro z
  obtain ⟨e, he, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B z
  have hemem : (e : logSpace K) ∈ unitLattice K := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)]
    exact e.property
  obtain ⟨u, -, hu⟩ := hemem
  refine ⟨u.toMul, ?_⟩
  change ‖logEmbedding K u + z‖ ≤ R
  change logEmbedding K u = (e : logSpace K) at hu
  rw [hu]
  exact hbound _ he

/-- The full logarithmic deviation from the geometric mean. -/
def logDeviation (x : mixedEmbedding.mixedSpace K) (w : InfinitePlace K) : ℝ :=
  Real.log (mixedEmbedding.normAtPlace w x) -
    Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹

/-- No place has been lost by dropping one coordinate from the logarithmic space. -/
theorem sum_mult_logDeviation {x : mixedEmbedding.mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace K, (w.mult : ℝ) * logDeviation x w = 0 := by
  classical
  have hnorm : Real.log (mixedEmbedding.norm x) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (mixedEmbedding.normAtPlace w x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod]
    · simp only [Real.log_pow]
    · intro w hw
      exact pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp hx w)
  have hmult : (∑ w : InfinitePlace K, (w.mult : ℝ)) = Module.finrank ℚ K := by
    exact_mod_cast (sum_mult_eq (K := K))
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  simp only [logDeviation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [← hnorm, hmult]
  field_simp
  ring

/-- A bound on the reduced logarithmic vector controls every infinite place,
including the distinguished omitted place. -/
theorem logDeviation_abs_le_of_logMap_norm_le
    {x : mixedEmbedding.mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0)
    {R : ℝ} (hR : 0 ≤ R) (h : ‖mixedEmbedding.logMap x‖ ≤ R) (w : InfinitePlace K) :
    |logDeviation x w| ≤ (Fintype.card (InfinitePlace K) : ℝ) * R := by
  classical
  have hmult (v : InfinitePlace K) : |logDeviation x v| ≤ |(v.mult : ℝ) * logDeviation x v| := by
    simp only [abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast (Nat.succ_le_of_lt mult_pos))
  have hcoord (v : {v : InfinitePlace K // v ≠ w₀}) :
      |(v.val.mult : ℝ) * logDeviation x v.val| ≤ R := by
    have hc := (norm_le_pi_norm (mixedEmbedding.logMap x) v).trans h
    exact hc
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  by_cases hw : w = w₀
  · have hs := sum_mult_logDeviation hx
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K)] at hs
    have heq : ((w₀ : InfinitePlace K).mult : ℝ) * logDeviation x w₀ =
        - ∑ v : {v : InfinitePlace K // v ≠ w₀}, (v.val.mult : ℝ) * logDeviation x v.val := by
      linarith
    rw [hw]
    apply (hmult _).trans
    rw [heq, abs_neg]
    calc
      _ ≤ ∑ v : {v : InfinitePlace K // v ≠ w₀},
          |(v.val.mult : ℝ) * logDeviation x v.val| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : {v : InfinitePlace K // v ≠ w₀}, R :=
        Finset.sum_le_sum fun v _ => hcoord v
      _ ≤ (Fintype.card (InfinitePlace K) : ℝ) * R := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast (Fintype.card_subtype_le
          (fun v : InfinitePlace K => v ≠ w₀))) hR
  · exact (hmult _).trans ((hcoord ⟨w, hw⟩).trans (le_mul_of_one_le_left hR hcard))

theorem logEmbedding_natPow (u : (𝓞 K)ˣ) (m : ℕ) :
    logEmbedding K (Additive.ofMul (u ^ m)) = (m : ℝ) • logEmbedding K (Additive.ofMul u) := by
  ext w
  simp only [logEmbedding_component, NumberField.Units.coe_pow, map_pow, Real.log_pow,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Closed logarithmic balancing by a totally positive unit kth power. -/
theorem exists_positive_unit_log_balance (K : Type*) [Field K] [NumberField K]
    (k : ℕ) (hk : 0 < k) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : mixedEmbedding.mixedSpace K,
      mixedEmbedding.norm x ≠ 0 → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧
        ∀ w : InfinitePlace K, |logDeviation ((u ^ k) • x) w| ≤ M := by
  classical
  obtain ⟨R, hR, hcover⟩ := exists_log_unit_covering_radius K
  let c : ℝ := 2 * k
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨(Fintype.card (InfinitePlace K) : ℝ) * (c * R),
    mul_pos (by exact_mod_cast Fintype.card_pos) (mul_pos hc hR), ?_⟩
  intro x hx
  let z : logSpace K := c⁻¹ • mixedEmbedding.logMap x
  obtain ⟨t, ht⟩ := hcover z
  refine ⟨t ^ 2, totallyPositive_unit_sq t, ?_⟩
  have heq : mixedEmbedding.logMap (((t ^ 2) ^ k) • x) =
      c • (logEmbedding K (Additive.ofMul t) + z) := by
    rw [mixedEmbedding.logMap_unit_smul _ hx, ← pow_mul, logEmbedding_natPow]
    ext w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, z, c, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  have hn : ‖mixedEmbedding.logMap (((t ^ 2) ^ k) • x)‖ ≤ c * R := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left ht hc.le
  intro w
  exact logDeviation_abs_le_of_logMap_norm_le
    (by rwa [mixedEmbedding.norm_unit_smul]) (mul_pos hc hR).le hn w

/-- The balancing constant is independent of the target and controls every
archimedean magnitude above and away from zero. -/
theorem exists_positive_unit_balance (K : Type*) [Field K] [NumberField K]
    (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : mixedEmbedding.mixedSpace K,
      mixedEmbedding.norm x ≠ 0 → ∃ u : (𝓞 K)ˣ,
        TotallyPositive (u : 𝓞 K) ∧ ∀ w : InfinitePlace K,
          C⁻¹ * (mixedEmbedding.norm x) ^ (1 / (Module.finrank ℚ K : ℝ)) ≤
            mixedEmbedding.normAtPlace w ((u ^ k) • x) ∧
          mixedEmbedding.normAtPlace w ((u ^ k) • x) ≤
            C * (mixedEmbedding.norm x) ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨M, hM, hbalance⟩ := exists_positive_unit_log_balance K k hk
  refine ⟨Real.exp M, (Real.one_le_exp_iff).mpr hM.le, ?_⟩
  intro x hx
  obtain ⟨u, hu, hbound⟩ := hbalance x hx
  refine ⟨u, hu, ?_⟩
  intro w
  have hnormpos : 0 < mixedEmbedding.norm x :=
    lt_of_le_of_ne (mixedEmbedding.norm_nonneg x) hx.symm
  have hplacepos : 0 < mixedEmbedding.normAtPlace w ((u ^ k) • x) :=
    lt_of_le_of_ne (mixedEmbedding.normAtPlace_nonneg _ _)
      (mixedEmbedding.norm_ne_zero_iff.mp (by rwa [mixedEmbedding.norm_unit_smul]) w).symm
  have hh := abs_le.mp (hbound w)
  simp only [logDeviation, mixedEmbedding.norm_unit_smul] at hh
  have hl : -M + Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹ ≤
      Real.log (mixedEmbedding.normAtPlace w ((u ^ k) • x)) := by linarith [hh.1]
  have hu' : Real.log (mixedEmbedding.normAtPlace w ((u ^ k) • x)) ≤
      M + Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹ := by linarith [hh.2]
  constructor
  · have he := Real.exp_le_exp.mpr hl
    simpa only [Real.exp_add, Real.exp_neg, Real.exp_log hplacepos,
      Real.rpow_def_of_pos hnormpos, one_div] using he
  · have he := Real.exp_le_exp.mpr hu'
    simpa only [Real.exp_add, Real.exp_log hplacepos,
      Real.rpow_def_of_pos hnormpos, one_div] using he

/-- Literal algebraic-integer specialization, with the project's actual absolute norm. -/
theorem exists_positive_unit_balance_integer (K : Type*) [Field K] [NumberField K]
    (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ν : 𝓞 K, ν ≠ 0 → ∃ u : (𝓞 K)ˣ,
      TotallyPositive (u : 𝓞 K) ∧ ∀ w : InfinitePlace K,
        C⁻¹ * absNorm ν ^ (1 / (Module.finrank ℚ K : ℝ)) ≤
          w (((u : 𝓞 K) ^ k * ν : 𝓞 K) : K) ∧
        w (((u : 𝓞 K) ^ k * ν : 𝓞 K) : K) ≤
          C * absNorm ν ^ (1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC, hbalance⟩ := exists_positive_unit_balance K k hk
  refine ⟨C, hC, ?_⟩
  intro ν hν
  have hνK : (ν : K) ≠ 0 := by exact_mod_cast hν
  have hn : mixedEmbedding.norm (mixedEmbedding K (ν : K)) = absNorm ν := by
    rw [mixedEmbedding.norm_eq_norm]
    simpa only [fieldAbsNorm, Rat.cast_abs] using fieldAbsNorm_integer ν
  have hpos : 0 < absNorm ν := by rw [← fieldAbsNorm_integer]; exact fieldAbsNorm_pos hνK
  obtain ⟨u, hu, hb⟩ := hbalance (mixedEmbedding K (ν : K)) (by rw [hn]; exact hpos.ne')
  refine ⟨u, hu, ?_⟩
  intro w
  have hemb : (u ^ k) • mixedEmbedding K (ν : K) =
      mixedEmbedding K ((((u : 𝓞 K) ^ k) * ν : 𝓞 K) : K) := by
    rw [mixedEmbedding.unitSMul_smul, ← map_mul]
    congr 1
  simpa only [hn, hemb, mixedEmbedding.normAtPlace_apply] using hb w

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_positive_unit_balance_integer
