import Waring.EndgameCompletionMinorReproduction

/-!
# Completing the projected moments to the actual Vinogradov count

Each additional real coefficient integral imposes exactly its next
integer power equation. Two such integrals turn the projected slices into
the same literal tuple count supplied by the verified critical theorem.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace Waring.EndgameCompletion
open FourierCompletion QuadraticModulation

theorem tuplePowerVector_succ_eq_iff {ι : Type*} {s : ℕ} (r : ℕ)
    (v : ι→ℤ) (x y : Fin s→ι) :
    tuplePowerVector (r+1) v x=tuplePowerVector (r+1) v y ↔
      tuplePowerVector r v x=tuplePowerVector r v y ∧
        powerDifference (fun i=>v (x i)) (fun i=>v (y i)) (r+1)=0 := by
  rw [tuplePowerVector_eq_iff,tuplePowerVector_eq_iff]
  constructor
  · intro h
    exact ⟨fun j hj=>h j (by omega),h (r+1) le_rfl⟩
  · rintro ⟨h,hn⟩ j hj
    by_cases hjr : j≤r
    · exact h j hjr
    · have he : j=r+1 := by omega
      simpa only [he] using hn

theorem projectedMoment_add_coefficient_expansion {ι : Type*} [Fintype ι]
    (r s : ℕ) (v : ι→ℤ) (w : ι→ℂ) (t : ℝ) :
    (projectedMoment r s v (fun n=>w n*e (t*(v n : ℝ)^(r+1))) : ℂ)=
      ∑ x : Fin s→ι,∑ y : Fin s→ι,
        (if tuplePowerVector r v x=tuplePowerVector r v y then
          tupleWeight w x*conj (tupleWeight w y) else 0)*
        fourier (powerDifference (fun i=>v (x i)) (fun i=>v (y i)) (r+1))
          (t : UnitAddCircle) := by
  classical
  rw [projectedMoment_gram]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : tuplePowerVector r v x=tuplePowerVector r v y
  · rw [if_pos h,if_pos h]
    have ht (z : Fin s→ι) : tupleWeight (fun n=>w n*e (t*(v n : ℝ)^(r+1))) z=
        tupleWeight w z*tupleWeight (fun n=>e (t*(v n : ℝ)^(r+1))) z :=
      Finset.prod_mul_distrib
    rw [ht,ht,map_mul]
    have hphase : tupleWeight (fun n=>e (t*(v n : ℝ)^(r+1))) x*
        conj (tupleWeight (fun n=>e (t*(v n : ℝ)^(r+1))) y)=
      fourier (powerDifference (fun i=>v (x i)) (fun i=>v (y i)) (r+1))
        (t : UnitAddCircle) := by
      rw [tupleWeight_e_pair,fourier_eq_e]
      congr 1
      simp only [powerDifference,GafniTao.wooleyPowerSum,Int.cast_sub,Int.cast_sum,
        Int.cast_pow,← Finset.mul_sum]
      ring
    calc
      _ = (tupleWeight w x*conj (tupleWeight w y))*
          (tupleWeight (fun n=>e (t*(v n : ℝ)^(r+1))) x*
            conj (tupleWeight (fun n=>e (t*(v n : ℝ)^(r+1))) y)) := by ring
      _ = _ := by rw [hphase]
  · rw [if_neg h,if_neg h,zero_mul]

/-- Adding one coefficient integral imposes precisely the next power
equation, with the same tuple weights. -/
theorem projectedMoment_add_coefficient {ι : Type*} [Fintype ι]
    (r s : ℕ) (v : ι→ℤ) (w : ι→ℂ) :
    (∫ t in (0 : ℝ)..1,
      projectedMoment r s v (fun n=>w n*e (t*(v n : ℝ)^(r+1))))=
      projectedMoment (r+1) s v w := by
  classical
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [projectedMoment_add_coefficient_expansion]
  have hi (x y : Fin s→ι) : IntervalIntegrable (fun t : ℝ=>
      (if tuplePowerVector r v x=tuplePowerVector r v y then
        tupleWeight w x*conj (tupleWeight w y) else 0)*
      fourier (powerDifference (fun i=>v (x i)) (fun i=>v (y i)) (r+1))
        (t : UnitAddCircle)) volume 0 1 :=
    (continuous_const.mul ((fourier _).continuous.comp (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
  have hinner (x : Fin s→ι) : IntervalIntegrable (fun t : ℝ=>∑ y : Fin s→ι,
      (if tuplePowerVector r v x=tuplePowerVector r v y then
        tupleWeight w x*conj (tupleWeight w y) else 0)*
      fourier (powerDifference (fun i=>v (x i)) (fun i=>v (y i)) (r+1))
        (t : UnitAddCircle)) volume 0 1 := by
    convert IntervalIntegrable.sum Finset.univ (fun y _=>hi x y) using 1
    funext t
    simp only [Finset.sum_apply]
  rw [intervalIntegral.integral_finset_sum (fun x _=>hinner x),projectedMoment_gram]
  apply Finset.sum_congr rfl
  intro x _
  rw [intervalIntegral.integral_finset_sum (fun y _=>hi x y)]
  apply Finset.sum_congr rfl
  intro y _
  rw [intervalIntegral.integral_const_mul,interval_integral_character]
  simp only [tuplePowerVector_succ_eq_iff]
  by_cases he : tuplePowerVector r v x=tuplePowerVector r v y <;>
    by_cases hd : powerDifference (fun i=>v (x i)) (fun i=>v (y i)) (r+1)=0 <;>
    simp only [he,hd,true_and,false_and,ite_true,ite_false,mul_one,mul_zero,zero_mul]

theorem projectedSlice_integral (r s N : ℕ) (θ : ℝ) :
    (∫ t in (0 : ℝ)..1,projectedSlice r s N t θ)=
      projectedMoment (r+1) s (positiveNode N)
        (fun n=>e (θ*(positiveNode N n : ℝ)^(r+2))) := by
  simpa only [projectedSlice,e_add] using projectedMoment_add_coefficient r s (positiveNode N)
    (fun n=>e (θ*(positiveNode N n : ℝ)^(r+2)))

theorem polynomialTorusSum_positive_eq_ford (k N : ℕ) (α : UnitAddTorus (Fin k)) :
    polynomialTorusSum k (positiveNode N) (fun _=>1) α=
      GafniTao.fordVinogradovWeylSum k N α := by
  unfold polynomialTorusSum finiteTorusSum GafniTao.fordVinogradovWeylSum
    GafniTao.fordVinogradovMonomial
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro n _
  apply congrArg (fun f : Fin k→ℤ=>UnitAddTorus.mFourier f α)
  funext j
  simp [positiveNode,GafniTao.fordVinogradovExponent]

theorem projectedMoment_positive_eq_count (k s N : ℕ) :
    projectedMoment k s (positiveNode N) (fun _=>1)=
      (GafniTao.fordVinogradovMomentNat s k N : ℝ) := by
  unfold projectedMoment
  simp_rw [polynomialTorusSum_positive_eq_ford]
  exact GafniTao.ford_vinogradov_torus_real_mean_eq s k N

/-- The completed double real-coefficient integral is exactly the
verified source's literal count, without a measure-normalization loss. -/
theorem projectedSlice_full_integral (r s N : ℕ) :
    (∫ θ in (0 : ℝ)..1,∫ t in (0 : ℝ)..1,projectedSlice r s N t θ)=
      (GafniTao.fordVinogradovMomentNat s (r+2) N : ℝ) := by
  simp_rw [projectedSlice_integral]
  have hh := projectedMoment_add_coefficient (r+1) s (positiveNode N) (fun _=>1)
  simp only [one_mul] at hh
  rw [hh]
  exact projectedMoment_positive_eq_count (r+2) s N

#print axioms projectedMoment_add_coefficient
#print axioms projectedSlice_full_integral
end Waring.EndgameCompletion
