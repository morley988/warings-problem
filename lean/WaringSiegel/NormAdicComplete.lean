import Mathlib.RingTheory.Henselian
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Algebraic completeness from shrinking ideal balls

This bridge proves the algebraic `IsAdicComplete` property needed by Mathlib's
Hensel theorem from actual metric completeness and an explicit description of
the powers of the ideal as shrinking closed balls.
-/

open Filter Topology

namespace WaringSiegel

theorem isAdicComplete_of_norm_balls
    {R : Type*} [NormedCommRing R] [CompleteSpace R]
    (I : Ideal R) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hballs : ∀ n : ℕ, ((I ^ n : Ideal R) : Set R) = Metric.closedBall 0 (q ^ n)) :
    IsAdicComplete I R := by
  have hmod (n : ℕ) (x y : R) :
      x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ ‖x - y‖ ≤ q ^ n := by
    rw [SModEq.sub_mem, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    change x - y ∈ ((I ^ n : Ideal R) : Set R) ↔ _
    rw [hballs n]
    simp only [Metric.mem_closedBall, dist_zero_right]
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  refine { haus' := ?_, prec' := ?_ }
  ·
    intro x hx
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg x)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    exact Filter.Eventually.of_forall (fun n => by simpa using (hmod n x 0).mp (hx n))
  ·
    intro f hf
    have hc : CauchySeq f := cauchySeq_of_le_tendsto_0' (fun n => q ^ n)
      (fun n m hnm => by simpa only [dist_eq_norm] using (hmod n _ _).mp (hf hnm)) hlim
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨L, fun n => (hmod n _ _).mpr ?_⟩
    apply le_of_tendsto (tendsto_const_nhds.sub hL).norm
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact (hmod n _ _).mp (hf hm)

/-- Converting the ideal-based Hensel theorem to the local-ring API is safe
because a unit remains a unit in the residue quotient. -/
theorem henselianLocalRing_of_isAdicComplete
    {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] : HenselianLocalRing R where
  is_henselian f hf a ha hder := by
    exact HenselianRing.is_henselian f hf a ha
      (hder.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))

end WaringSiegel

#print axioms WaringSiegel.isAdicComplete_of_norm_balls
#print axioms WaringSiegel.henselianLocalRing_of_isAdicComplete
