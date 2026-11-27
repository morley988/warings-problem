import WaringSiegel.WSL4MajorCharacters

/-! # Quantitative actual conductor truncation from a weighted absolute moment

The input is explicitly the remaining weighted conductor moment. The
output concerns the literal rational-center cutoff used by the arcs and
the actual all-degree singular series, with no changed index system.
-/
noncomputable section
set_option maxHeartbeats 1000000
open NumberField WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem rationalTraceCenter_norm_one_le (q : RationalTraceCenter K) :
    (1:ℝ) ≤ ((rationalTraceCenterConductor q).absNorm:ℝ) := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot (rationalTraceCenterConductor q)
    (rationalTraceCenterConductor_ne_zero q)
  have hp : 0 < (rationalTraceCenterConductor q).absNorm :=
    Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff _).mpr inferInstance)
  exact_mod_cast Nat.succ_le_of_lt hp

theorem rationalCenterPowerContribution_tsum (k n : ℕ) (target : 𝓞 K) :
    (∑' q : RationalTraceCenter K,rationalCenterPowerContribution k n q target) =
      powerSingularSeries k n target := by
  exact cubicConductorCharacterEquivRationalCenter.symm.tsum_eq
    (fun c => powerCharacterContribution k n c target)

theorem rationalPower_norm_summable_of_weighted
    (k n : ℕ) (target : 𝓞 K) (δ : ℝ) (hδ : 0≤δ)
    (hs : Summable (fun q : RationalTraceCenter K =>
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖rationalCenterPowerContribution k n q target‖)) :
    Summable (fun q : RationalTraceCenter K => ‖rationalCenterPowerContribution k n q target‖) := by
  apply hs.of_nonneg_of_le (fun q => norm_nonneg _)
  intro q
  exact le_mul_of_one_le_left (norm_nonneg _)
    (Real.one_le_rpow (rationalTraceCenter_norm_one_le q) hδ)

theorem rationalPower_finite_mass_le
    (k n : ℕ) (target : 𝓞 K) (δ M : ℝ)
    (hs : Summable (fun q : RationalTraceCenter K =>
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖rationalCenterPowerContribution k n q target‖))
    (hb : (∑' q : RationalTraceCenter K,
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖rationalCenterPowerContribution k n q target‖)≤M)
    (S : Finset (RationalTraceCenter K)) :
    (∑ q ∈ S,((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
      ‖rationalCenterPowerContribution k n q target‖)≤M := by
  exact (hs.sum_le_tsum S (fun q hq => by positivity)).trans hb

theorem rationalPower_conductor_truncation
    (k n : ℕ) (target : 𝓞 K) (δ M : ℝ) (hδ : 0≤δ)
    (hs : Summable (fun q : RationalTraceCenter K =>
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖rationalCenterPowerContribution k n q target‖))
    (hb : (∑' q : RationalTraceCenter K,
      ((rationalTraceCenterConductor q).absNorm:ℝ)^δ *
        ‖rationalCenterPowerContribution k n q target‖)≤M)
    (L : ℝ) (hL : 0<L) :
    ‖powerSingularSeries k n target-
      ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,rationalCenterPowerContribution k n q target‖≤M/L^δ := by
  let S : Set (RationalTraceCenter K) := {q | q∉rationalCentersUpTo ⌊L⌋₊}
  have hn := rationalPower_norm_summable_of_weighted k n target δ hδ hs
  have hns := hn.subtype S
  have hss := hs.subtype S
  change Summable (fun q : S => ‖rationalCenterPowerContribution k n q.1 target‖) at hns
  change Summable (fun q : S => ((rationalTraceCenterConductor q.1).absNorm:ℝ)^δ *
    ‖rationalCenterPowerContribution k n q.1 target‖) at hss
  have htail : powerSingularSeries k n target-
      ∑ q ∈ rationalCentersUpTo ⌊L⌋₊,rationalCenterPowerContribution k n q target =
      ∑' q : S,rationalCenterPowerContribution k n q.1 target := by
    have he := hn.of_norm.sum_add_tsum_subtype_compl (rationalCentersUpTo (K := K) ⌊L⌋₊)
    rw [rationalCenterPowerContribution_tsum] at he
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he.symm)
  rw [htail]
  apply (norm_tsum_le_tsum_norm hns).trans
  have hsub : (∑' q : S,
      ((rationalTraceCenterConductor q.1).absNorm:ℝ)^δ *
        ‖rationalCenterPowerContribution k n q.1 target‖)≤M :=
    (Summable.tsum_subtype_le _ S (fun q => by positivity) hs).trans hb
  have hpoint (q : S) :
      L^δ * ‖rationalCenterPowerContribution k n q.1 target‖≤
        ((rationalTraceCenterConductor q.1).absNorm:ℝ)^δ *
          ‖rationalCenterPowerContribution k n q.1 target‖ := by
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

#print axioms rationalPower_norm_summable_of_weighted
#print axioms rationalPower_conductor_truncation
end WaringSiegel.WSL4
