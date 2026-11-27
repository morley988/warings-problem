import Waring.FirstStageRecurrence
import Waring.RestrictedSmoothUniformity
import Waring.FourthMomentSeed

/-!
# The first-stage endpoint bootstrap

At M^k>=P every extracted coefficient has m>M, so the literal next height
range is empty. This closes the endpoint recurrence without assuming an
auxiliary moment estimate and provides an initial admissible seed.
-/

noncomputable section
open scoped BigOperators
namespace Waring.FirstStageTransport
open SmoothMoments FirstDifferenceSecond
open SeedCompletionBackwardCount SeedCompletionBackwardAggregate
open SeedCompletionSharpBackward PolicyCompletionHolder

theorem initialNextDomain_eq_empty {k : ℕ} (hk : 0 < k) {P R M : ℝ}
    (hP : 1 ≤ P) (hM : 1 ≤ M) (hMk : P ≤ M^k) :
    initialNextDomain k P R M = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hw,hzlo,hzhi,hhlo,hhhi⟩ := initialNextDomain_bounds hp
  have hMw : M < (p.1.2 : ℝ) := (Finset.mem_filter.mp hw).2.1
  have hwpow : P < (p.1.2 : ℝ)^k := hMk.trans_lt
    (pow_lt_pow_left₀ hMw (zero_le_one.trans hM) hk.ne')
  have hwposN : 0 < p.1.2 := by
    exact_mod_cast (zero_lt_one.trans (hM.trans_lt hMw))
  have hwpos : 0 < (p.1.2 : ℤ)^k := pow_pos (by exact_mod_cast hwposN) _
  have hhprod := (Int.le_ediv_iff_mul_le hwpos).mp hhhi
  have hprod : (p.1.2 : ℤ)^k ≤ (⌊P⌋₊ : ℤ) := by nlinarith
  have hprodR : (p.1.2 : ℝ)^k ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast hprod
  exact (not_le_of_gt hwpow) (hprodR.trans (Nat.floor_le (zero_le_one.trans hP)))

theorem firstCross_eq_zero {k : ℕ} (hk : 0 < k) (s : ℕ) {P R M : ℝ}
    (hP : 1 ≤ P) (hM : 1 ≤ M) (hMk : P ≤ M^k) :
    firstCross k s P R M = 0 := by
  have he := initialNextDomain_eq_empty hk (R := R) hP hM hMk
  unfold firstCross nextSmoothCrossIntegral aggregateNextCrossIntegral
  change (∫ x in (0 : ℝ)..1,
    ‖frequencySum (initialNextDomain k P R M) _ x‖*_) = 0
  simp [he,frequencySum]

end Waring.FirstStageTransport
