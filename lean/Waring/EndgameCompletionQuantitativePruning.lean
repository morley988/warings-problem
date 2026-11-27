import Waring.EndgameCompletionQuantitativeTail

/-!
# Power saving on the actual ordinary pruning region

Weighted convergence of the complete-coefficient series and decay of the
singular integral give uniform power saving in the integer rectangle cutoff.
The broad-arc approximation error is absorbed whenever the cutoff is at most
the ordinary length scale.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Waring.EndgameCompletion
open MixedEndgame

theorem pruningDecay_le_half (k : ℕ) (hk : 1≤k) : pruningDecay k≤1/2 := by
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hkr : (1 : ℝ)≤k := by exact_mod_cast hk
  have hh := pruningDecay_mul (show 0<k by omega)
  have hd := (pruningDecay_pos (show 0<k by omega)).le
  nlinarith

theorem ordinary_pruning_error_le (k s : ℕ) (hk : 1≤k) (hks : k≤s)
    {P : ℝ} (hP : 1≤P) (N : ℕ) (hN : 1≤N) (hNP : (N : ℝ)≤P) :
    P^((s : ℝ)-k-1/2)≤P^(s-k)*(N : ℝ)^(-pruningDecay k) := by
  have hp : 0<P := zero_lt_one.trans_le hP
  have hn : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hd : 0≤pruningDecay k := (pruningDecay_pos (show 0<k by omega)).le
  have he : P^((s : ℝ)-k-1/2)=P^(s-k)*P^(-(1/2 : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hp,Nat.cast_sub hks]
    congr 1
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hp.le _)
  exact (Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg (pruningDecay_le_half k hk))).trans
    (Real.rpow_le_rpow_of_nonpos hn hNP (neg_nonpos.mpr hd))

/-- The true ordinary integral over `ordinaryBroadMajor \ rectangleCoreGlobal`
has a fixed negative power of its rectangle cutoff, with no epsilon loss. -/
theorem ordinary_pruning_moment_power_bound (k s : ℕ) (hk : 2≤k) (hs : 11≤s)
    (hks : k+2≤s) (hsum : Summable (completeCoefficient k s))
    (hweighted : Summable (weightedCompleteCoefficient k s)) :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P → ∀ N : ℕ,1≤N → (N : ℝ)≤P →
      ordinaryPruningMoment k s P N≤C*P^(s-k)*(N : ℝ)^(-pruningDecay k) := by
  obtain ⟨Cm,hCm,hm⟩ := normalizedPruningModelMass_power_tail k s hk hks hsum hweighted
  obtain ⟨Ce,hCe,he⟩ := ordinary_pruning_moment_bound k s hk hs (by omega) hsum
  refine ⟨(2*(2 : ℝ)^(s-1))*(Cm+Ce^s),by positivity,?_⟩
  intro P hP N hN hNP
  have hp := zero_lt_one.trans_le hP
  calc
    _ ≤ (2*(2 : ℝ)^(s-1))*(P^(s-k)*normalizedPruningModelMass k s N+
        Ce^s*P^((s : ℝ)-k-1/2)) := he P hP N
    _ ≤ (2*(2 : ℝ)^(s-1))*(P^(s-k)*(Cm*(N : ℝ)^(-pruningDecay k))+
        Ce^s*(P^(s-k)*(N : ℝ)^(-pruningDecay k))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_le_mul_of_nonneg_left (hm N hN) (pow_nonneg hp.le _))
        (mul_le_mul_of_nonneg_left (ordinary_pruning_error_le k s (by omega) (by omega)
          hP N hN hNP) (pow_nonneg hCe.le _))
    _ = _ := by ring

theorem degree8_ordinary_pruning12_power_bound :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P → ∀ N : ℕ,1≤N → (N : ℝ)≤P →
      ordinaryPruningMoment 8 12 P N≤C*P^4*(N : ℝ)^(-(1/16 : ℝ)) := by
  convert ordinary_pruning_moment_power_bound 8 12 (by norm_num) (by norm_num) (by norm_num)
    (degree8_completeCoefficient_summable 12 (by norm_num))
    (degree8_weightedCompleteCoefficient_summable 12 (by norm_num)) using 1 <;>
    norm_num [pruningDecay]

theorem degree9_ordinary_pruning11_power_bound :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P → ∀ N : ℕ,1≤N → (N : ℝ)≤P →
      ordinaryPruningMoment 9 11 P N≤C*P^2*(N : ℝ)^(-(1/18 : ℝ)) := by
  convert ordinary_pruning_moment_power_bound 9 11 (by norm_num) (by norm_num) (by norm_num)
    (degree9_completeCoefficient_summable 11 (by norm_num))
    (degree9_weightedCompleteCoefficient_summable 11 (by norm_num)) using 1 <;>
    norm_num [pruningDecay]

theorem degree8_ordinary_pruning12_quantitative :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P → ∀ N : ℕ,1≤N → (N : ℝ)≤P →
      ordinaryArcMoment 8 12 P (ordinaryPruning 8 P N)≤
        ENNReal.ofReal (C*P^4*(N : ℝ)^(-(1/16 : ℝ))) := by
  obtain ⟨C,hC,h⟩ := degree8_ordinary_pruning12_power_bound
  refine ⟨C,hC,fun P hP N hN hNP=>?_⟩
  rw [ordinaryArcMoment_pruning_eq]
  exact ENNReal.ofReal_le_ofReal (h P hP N hN hNP)

theorem degree9_ordinary_pruning11_quantitative :
    ∃ C : ℝ,0<C ∧ ∀ P : ℝ,1≤P → ∀ N : ℕ,1≤N → (N : ℝ)≤P →
      ordinaryArcMoment 9 11 P (ordinaryPruning 9 P N)≤
        ENNReal.ofReal (C*P^2*(N : ℝ)^(-(1/18 : ℝ))) := by
  obtain ⟨C,hC,h⟩ := degree9_ordinary_pruning11_power_bound
  refine ⟨C,hC,fun P hP N hN hNP=>?_⟩
  rw [ordinaryArcMoment_pruning_eq]
  exact ENNReal.ofReal_le_ofReal (h P hP N hN hNP)

#print axioms degree8_ordinary_pruning12_quantitative
#print axioms degree9_ordinary_pruning11_quantitative
end Waring.EndgameCompletion
