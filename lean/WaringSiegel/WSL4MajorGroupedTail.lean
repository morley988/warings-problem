import WaringSiegel.WSL4MajorGroupedCharacters
import WaringSiegel.WSL4PowerIdealSeries

/-! # Quantitative ideal-conductor truncation from a weighted aggregate moment

The input is explicitly the remaining weighted conductor moment. The
output concerns the literal rational-center cutoff used by the arcs and
the conductor-ideal ordered all-degree series. No character-tsum identification is claimed.
-/
noncomputable section
set_option maxHeartbeats 1000000
open NumberField WaringSiegel.WSL4Local
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem nonzeroIdeal_norm_one_le (I : {I : Ideal (𝓞 K) // I≠0}) :
    (1:ℝ)≤(I.1.absNorm:ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp I.2)

theorem idealPower_norm_summable_of_weighted
    (k n : ℕ) (target : 𝓞 K) (δ : ℝ) (hδ : 0≤δ)
    (hs : Summable (fun q : {I : Ideal (𝓞 K) // I≠0} =>
      (q.1.absNorm:ℝ)^δ *
        ‖idealPrimitivePowerCoefficient k n q.1 q.2 target‖)) :
    Summable (fun q : {I : Ideal (𝓞 K) // I≠0} => ‖idealPrimitivePowerCoefficient k n q.1 q.2 target‖) := by
  apply hs.of_nonneg_of_le (fun q => norm_nonneg _)
  intro q
  exact le_mul_of_one_le_left (norm_nonneg _)
    (Real.one_le_rpow (nonzeroIdeal_norm_one_le q) hδ)

theorem idealPower_finite_mass_le
    (k n : ℕ) (target : 𝓞 K) (δ M : ℝ)
    (hs : Summable (fun q : {I : Ideal (𝓞 K) // I≠0} =>
      (q.1.absNorm:ℝ)^δ *
        ‖idealPrimitivePowerCoefficient k n q.1 q.2 target‖))
    (hb : (∑' q : {I : Ideal (𝓞 K) // I≠0},
      (q.1.absNorm:ℝ)^δ *
        ‖idealPrimitivePowerCoefficient k n q.1 q.2 target‖)≤M)
    (S : Finset ({I : Ideal (𝓞 K) // I≠0})) :
    (∑ q ∈ S,(q.1.absNorm:ℝ)^δ *
      ‖idealPrimitivePowerCoefficient k n q.1 q.2 target‖)≤M := by
  exact (hs.sum_le_tsum S (fun q hq => by positivity)).trans hb

theorem idealPower_conductor_truncation
    (k n : ℕ) (target : 𝓞 K) (δ M : ℝ) (hδ : 0≤δ)
    (hs : Summable (fun q : {I : Ideal (𝓞 K) // I≠0} =>
      (q.1.absNorm:ℝ)^δ *
        ‖idealPrimitivePowerCoefficient k n q.1 q.2 target‖))
    (hb : (∑' q : {I : Ideal (𝓞 K) // I≠0},
      (q.1.absNorm:ℝ)^δ *
        ‖idealPrimitivePowerCoefficient k n q.1 q.2 target‖)≤M)
    (L : ℝ) (hL : 0<L) :
    ‖powerIdealSingularSeries k n target-
      ∑ q ∈ cubicConductorCutoff ⌊L⌋₊,idealPrimitivePowerCoefficient k n q.1 q.2 target‖≤M/L^δ := by
  let S : Set ({I : Ideal (𝓞 K) // I≠0}) := {q | q∉cubicConductorCutoff ⌊L⌋₊}
  have hn := idealPower_norm_summable_of_weighted k n target δ hδ hs
  have hns := hn.subtype S
  have hss := hs.subtype S
  change Summable (fun q : S => ‖idealPrimitivePowerCoefficient k n q.1.1 q.1.2 target‖) at hns
  change Summable (fun q : S => (q.1.1.absNorm:ℝ)^δ *
    ‖idealPrimitivePowerCoefficient k n q.1.1 q.1.2 target‖) at hss
  have htail : powerIdealSingularSeries k n target-
      ∑ q ∈ cubicConductorCutoff ⌊L⌋₊,idealPrimitivePowerCoefficient k n q.1 q.2 target =
      ∑' q : S,idealPrimitivePowerCoefficient k n q.1.1 q.1.2 target := by
    have he := hn.of_norm.sum_add_tsum_subtype_compl (cubicConductorCutoff (K := K) ⌊L⌋₊)
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he.symm)
  rw [htail]
  apply (norm_tsum_le_tsum_norm hns).trans
  have hsub : (∑' q : S,
      (q.1.1.absNorm:ℝ)^δ *
        ‖idealPrimitivePowerCoefficient k n q.1.1 q.1.2 target‖)≤M :=
    (Summable.tsum_subtype_le _ S (fun q => by positivity) hs).trans hb
  have hpoint (q : S) :
      L^δ * ‖idealPrimitivePowerCoefficient k n q.1.1 q.1.2 target‖≤
        (q.1.1.absNorm:ℝ)^δ *
          ‖idealPrimitivePowerCoefficient k n q.1.1 q.1.2 target‖ := by
    have hnorm : L≤(q.1.1.absNorm:ℝ) := by
      by_contra h
      apply q.2
      rw [mem_cubicConductorCutoff]
      exact Nat.le_floor (le_of_lt (lt_of_not_ge h))
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hL.le hnorm hδ) (norm_nonneg _)
  have hsum := (hns.mul_left (L^δ)).tsum_le_tsum hpoint hss
  rw [hns.tsum_mul_left] at hsum
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL δ)).mpr
  simpa only [mul_comm] using hsum.trans hsub

#print axioms idealPower_norm_summable_of_weighted
#print axioms idealPower_conductor_truncation
end WaringSiegel.WSL4
