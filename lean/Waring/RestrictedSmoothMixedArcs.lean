import Waring.RestrictedSmoothArcOperations
import Waring.RestrictedSmoothPointwiseLoss

/-! # Actual mixed-prime arc means controlled by shorter complete moments -/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Waring.RestrictedSmoothArcs
open SmoothMoments RestrictedSmoothFactorization

theorem continuous_mixedPrimeWeyl (k q π : ℕ) (X R : ℝ) :
    Continuous (mixedPrimeWeyl k q π X R) :=
  continuous_finset_sum _ (fun p _ => continuous_phase k (p.1*p.2))

theorem periodic_mixedPrimeWeyl (k q π : ℕ) (X R : ℝ) :
    Function.Periodic (mixedPrimeWeyl k q π X R) 1 := by
  intro x
  unfold mixedPrimeWeyl
  exact Finset.sum_congr rfl (fun p _ => periodic_phase k (p.1*p.2) x)

theorem continuous_scaled_smooth_norm (k s c : ℕ) (Y R : ℝ) :
    Continuous (fun x : ℝ => ‖smoothWeyl k Y R ((c : ℝ)*x)‖^s) :=
  ((continuous_smoothWeyl k Y R).comp (continuous_const.mul continuous_id)).norm.pow s

theorem periodic_scaled_smooth_norm (k s c : ℕ) (Y R : ℝ) :
    Function.Periodic (fun x : ℝ => ‖smoothWeyl k Y R ((c : ℝ)*x)‖^s) 1 := by
  intro x
  dsimp only
  rw [mul_add,mul_one]
  have h := (periodic_smoothWeyl k Y R).nat_mul c ((c : ℝ)*x)
  simpa only [mul_one] using congrArg (fun z : ℂ => ‖z‖^s) h

def shorterMomentIntegrand (k s π : ℕ) (X R x : ℝ) : ℝ :=
  ∑ z ∈ smoothNumbers X R,‖smoothWeyl k (X/(z : ℝ)) π ((z : ℝ)^k*x)‖^s

theorem continuous_shorterMomentIntegrand (k s π : ℕ) (X R : ℝ) :
    Continuous (shorterMomentIntegrand k s π X R) := by
  unfold shorterMomentIntegrand
  apply continuous_finset_sum
  intro z hz
  simpa only [Nat.cast_pow] using continuous_scaled_smooth_norm k s (z^k) (X/z) π

theorem sum_shorter_arc_integrals_le (S : Finset ℕ+) {Q δ : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hsmall : 4*Q*δ ≤ 1)
    (hQ : ∀ q ∈ S,(q : ℝ) ≤ Q) (k s π : ℕ) (X R : ℝ) :
    (∑ q ∈ S,rationalArcSum (q : ℕ) (shorterMomentIntegrand k s π X R) δ) ≤
      3*∑ z ∈ smoothNumbers X R,smoothMoment k s (X/(z : ℝ)) π := by
  have hcont (z : ℕ) : Continuous (fun x : ℝ =>
      ‖smoothWeyl k (X/(z : ℝ)) π ((z : ℝ)^k*x)‖^s) := by
    simpa only [Nat.cast_pow] using continuous_scaled_smooth_norm k s (z^k) (X/z) π
  have heq (q : ℕ+) := rationalArcSum_finset_sum (smoothNumbers X R) (q : ℕ)
    (fun z x => ‖smoothWeyl k (X/(z : ℝ)) π ((z : ℝ)^k*x)‖^s) δ (fun z _ => hcont z)
  unfold shorterMomentIntegrand
  simp_rw [heq]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hz0 := (mem_smoothNumbers.mp hz).1.1
  have hper : Function.Periodic (fun x : ℝ =>
      ‖smoothWeyl k (X/(z : ℝ)) π ((z : ℝ)^k*x)‖^s) 1 := by
    simpa only [Nat.cast_pow] using periodic_scaled_smooth_norm k s (z^k) (X/z) π
  have h := sum_rationalArcSum_le S hδ hδ1 hsmall hQ (hcont z) hper (fun _ => by positivity)
  have hid := smoothMoment_integer_dilation k s (z^k) (pow_pos hz0 k) (X/z) π
  simp only [Nat.cast_pow] at hid
  rw [hid] at h
  exact h

/-- The q-dependent mixed-prime sum has a uniform restricted mean bound.
All q-supported sparsity, residue arcs and shorter moments are actual. -/
theorem mixedPrimeWeyl_arcs_epsilon (k : ℕ) {s : ℕ} (hs : 1 ≤ s)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P → ∀ S : Finset ℕ+,∀ Q δ : ℝ,
      0 ≤ δ → δ ≤ 1 → 4*Q*δ ≤ 1 →
      (∀ q ∈ S,(q : ℝ) ≤ Q) → (∀ q ∈ S,(q : ℝ) ≤ P^B) →
      ∀ X R : ℝ,0 ≤ X → X ≤ P → ∀ π : ℕ,(π : ℝ) ≤ R →
      (∑ q ∈ S,rationalArcSum (q : ℕ) (fun x => ‖mixedPrimeWeyl k q π X R x‖^s) δ) ≤
        C*P^ε*∑ z ∈ smoothNumbers X R,smoothMoment k s (X/(z : ℝ)) π := by
  obtain ⟨D,hD,hbound⟩ := mixedPrimeWeyl_epsilon k hs hB hε
  refine ⟨3*D,by positivity,?_⟩
  intro P hP S Q δ hδ hδ1 hsmall hQ hqP X R hX hXP π hπR
  have hG := continuous_shorterMomentIntegrand k s π X R
  calc
    _ ≤ ∑ q ∈ S,rationalArcSum (q : ℕ)
        (fun x => D*P^ε*shorterMomentIntegrand k s π X R x) δ := by
      apply Finset.sum_le_sum
      intro q hq
      apply rationalArcSum_mono q hδ ((continuous_mixedPrimeWeyl k q π X R).norm.pow s)
        (continuous_const.mul hG)
      exact fun x => hbound P hP q q.pos (hqP q hq) X R hX hXP π hπR x
    _ = D*P^ε*∑ q ∈ S,rationalArcSum (q : ℕ) (shorterMomentIntegrand k s π X R) δ := by
      simp_rw [rationalArcSum_const_mul]
      exact (Finset.mul_sum _ _ _).symm
    _ ≤ D*P^ε*(3*∑ z ∈ smoothNumbers X R,smoothMoment k s (X/(z : ℝ)) π) :=
      mul_le_mul_of_nonneg_left (sum_shorter_arc_integrals_le S hδ hδ1 hsmall hQ k s π X R)
        (by positivity)
    _ = _ := by ring

#print axioms mixedPrimeWeyl_arcs_epsilon
end Waring.RestrictedSmoothArcs
