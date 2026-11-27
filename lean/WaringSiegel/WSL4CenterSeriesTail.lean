import WaringSiegel.WSL4MajorSeriesTail

/-! # Weighted conductor tails for an arbitrary literal rational-center coefficient -/
noncomputable section
set_option maxHeartbeats 1000000
open NumberField
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem rationalCenterSeries_norm_summable_of_weighted
    (f : RationalTraceCenter K → ℂ) (δ : ℝ) (hδ : 0≤δ)
    (hs : Summable (fun q : RationalTraceCenter K =>
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖f q‖)) :
    Summable (fun q : RationalTraceCenter K => ‖f q‖) := by
  apply hs.of_nonneg_of_le (fun q => norm_nonneg _)
  intro q
  exact le_mul_of_one_le_left (norm_nonneg _)
    (Real.one_le_rpow (rationalTraceCenter_norm_one_le q) hδ)

theorem rationalCenterSeries_finite_mass_le
    (f : RationalTraceCenter K → ℂ) (δ M : ℝ)
    (hs : Summable (fun q : RationalTraceCenter K =>
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖f q‖))
    (hb : (∑' q : RationalTraceCenter K,
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖f q‖)≤M)
    (S : Finset (RationalTraceCenter K)) :
    (∑ q ∈ S,((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
      ‖f q‖)≤M := by
  exact (hs.sum_le_tsum S (fun q hq => by positivity)).trans hb

theorem rationalCenterSeries_conductor_truncation
    (f : RationalTraceCenter K → ℂ) (δ M : ℝ) (hδ : 0≤δ)
    (hs : Summable (fun q : RationalTraceCenter K =>
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖f q‖))
    (hb : (∑' q : RationalTraceCenter K,
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖f q‖)≤M)
    (L : ℝ) (hL : 0<L) :
    ‖(∑' q, f q)-
      ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,f q‖≤M/L^δ := by
  let S : Set (RationalTraceCenter K) := {q | q∉rationalCentersUpTo ⌊L⌋₊}
  have hn := rationalCenterSeries_norm_summable_of_weighted f δ hδ hs
  have hns := hn.subtype S
  have hss := hs.subtype S
  change Summable (fun q : S => ‖f q.1‖) at hns
  change Summable (fun q : S => ((rationalTraceCenterConductor q.1).absNorm:ℝ)^δ *
    ‖f q.1‖) at hss
  have htail : (∑' q, f q)-
      ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,f q =
      ∑' q : S,f q.1 := by
    have he := hn.of_norm.sum_add_tsum_subtype_compl (rationalCentersUpTo (K := K) ⌊L⌋₊)
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he.symm)
  rw [htail]
  apply (norm_tsum_le_tsum_norm hns).trans
  have hsub : (∑' q : S,
      ((rationalTraceCenterConductor q.1).absNorm:ℝ)^δ *
        ‖f q.1‖)≤M :=
    (Summable.tsum_subtype_le _ S (fun q => by positivity) hs).trans hb
  have hpoint (q : S) :
      L^δ * ‖f q.1‖≤
        ((rationalTraceCenterConductor q.1).absNorm:ℝ)^δ *
          ‖f q.1‖ := by
    have hnorm : L≤((rationalTraceCenterConductor q.1).absNorm:ℝ) := by
      by_contra h
      apply q.2
      rw [mem_rationalCentersUpTo]
      exact Nat.le_floor (le_of_lt (lt_of_not_ge h))
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hL.le hnorm hδ) (norm_nonneg _)
  have hsum := (hns.mul_left (L^δ)).tsum_le_tsum hpoint hss
  rw [hns.tsum_mul_left] at hsum
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL δ)).mpr
  simpa only [mul_comm] using hsum.trans hsub

#print axioms rationalCenterSeries_norm_summable_of_weighted
#print axioms rationalCenterSeries_conductor_truncation
end WaringSiegel.WSL4Local
