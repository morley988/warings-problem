import Waring.EndgameCompletionMinorMoments

/-!
# Translation of the actual lower-degree Vinogradov constraints

The zero-th power difference vanishes because both tuples have equal
length. The lower equations are invariant under every common integer
translation. After they vanish, the top two differences have exactly the
two-term binomial form used by the minor-arc completion argument.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Waring.EndgameCompletion
open GafniTao QuadraticModulation

def powerDifference {s : ℕ} (x y : Fin s→ℤ) (j : ℕ) : ℤ :=
  wooleyPowerSum x j-wooleyPowerSum y j

@[simp] theorem powerDifference_zero {s : ℕ} (x y : Fin s→ℤ) :
    powerDifference x y 0=0 := by simp [powerDifference,wooleyPowerSum]

theorem powerDifference_translate {s : ℕ} (x y : Fin s→ℤ) (c : ℤ) (j : ℕ) :
    powerDifference (fun i=>x i+c) (fun i=>y i+c) j=
      ∑ m∈Finset.range (j+1),(j.choose m : ℤ)*c^(j-m)*powerDifference x y m := by
  simpa only [powerDifference,one_mul,one_pow,mul_one] using
    wooleyPowerSum_affine_sub x y 1 c j

theorem tuplePowerVector_eq_iff {ι : Type*} {s : ℕ} (r : ℕ) (v : ι→ℤ)
    (x y : Fin s→ι) :
    tuplePowerVector r v x=tuplePowerVector r v y ↔
      ∀ j : ℕ,j≤r → powerDifference (fun i=>v (x i)) (fun i=>v (y i)) j=0 := by
  constructor
  · intro he j hj
    rcases j with _|j
    · simp
    · have h := congrFun he (⟨j,by omega⟩ : Fin r)
      exact sub_eq_zero.mpr h
  · intro he
    ext j
    exact sub_eq_zero.mp (he (j.val+1) (by omega))

theorem lower_power_difference_translate {s : ℕ} (r : ℕ)
    (x y : Fin s→ℤ) (c : ℤ)
    (h : ∀ j : ℕ,j≤r → powerDifference x y j=0) :
    ∀ j : ℕ,j≤r → powerDifference (fun i=>x i+c) (fun i=>y i+c) j=0 := by
  intro j hj
  rw [powerDifference_translate]
  apply Finset.sum_eq_zero
  intro m hm
  rw [h m (by have hmj := Finset.mem_range.mp hm; omega),mul_zero]

theorem lower_power_difference_translate_iff {s : ℕ} (r : ℕ)
    (x y : Fin s→ℤ) (c : ℤ) :
    (∀ j : ℕ,j≤r → powerDifference (fun i=>x i+c) (fun i=>y i+c) j=0) ↔
      ∀ j : ℕ,j≤r → powerDifference x y j=0 := by
  constructor
  · intro h
    simpa only [add_neg_cancel_right] using lower_power_difference_translate r
      (fun i=>x i+c) (fun i=>y i+c) (-c) h
  · exact lower_power_difference_translate r x y c

theorem tuplePowerVector_translate_eq_iff {ι : Type*} {s : ℕ} (r : ℕ)
    (v : ι→ℤ) (x y : Fin s→ι) (c : ℤ) :
    tuplePowerVector r (fun n=>v n+c) x=tuplePowerVector r (fun n=>v n+c) y ↔
      tuplePowerVector r v x=tuplePowerVector r v y := by
  rw [tuplePowerVector_eq_iff,tuplePowerVector_eq_iff]
  exact lower_power_difference_translate_iff r _ _ c

theorem powerDifference_translate_next {s : ℕ} (r : ℕ) (x y : Fin s→ℤ)
    (c : ℤ) (h : ∀ j : ℕ,j≤r → powerDifference x y j=0) :
    powerDifference (fun i=>x i+c) (fun i=>y i+c) (r+1)=
      powerDifference x y (r+1) := by
  rw [powerDifference_translate,Finset.sum_range_succ]
  have hz : (∑ m∈Finset.range (r+1),((r+1).choose m : ℤ)*
      c^(r+1-m)*powerDifference x y m)=0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [h m (by have hmj := Finset.mem_range.mp hm; omega),mul_zero]
  rw [hz]
  simp

theorem powerDifference_translate_two {s : ℕ} (r : ℕ) (x y : Fin s→ℤ)
    (c : ℤ) (h : ∀ j : ℕ,j≤r → powerDifference x y j=0) :
    powerDifference (fun i=>x i+c) (fun i=>y i+c) (r+2)=
      powerDifference x y (r+2)+(r+2 : ℕ)*c*powerDifference x y (r+1) := by
  rw [powerDifference_translate,Finset.sum_range_succ,Finset.sum_range_succ]
  have hz : (∑ m∈Finset.range (r+1),((r+2).choose m : ℤ)*
      c^(r+2-m)*powerDifference x y m)=0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [h m (by have hmj := Finset.mem_range.mp hm; omega),mul_zero]
  rw [hz]
  simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,pow_zero,mul_one,
    zero_add,Nat.add_sub_add_left,Nat.choose_succ_self_right]
  ring

theorem prod_e {ι : Type*} (S : Finset ι) (f : ι→ℝ) :
    (∏ i∈S,e (f i))=e (∑ i∈S,f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [e]
  | @insert i S hi ih => rw [Finset.prod_insert hi,Finset.sum_insert hi,e_add,ih]

theorem tupleWeight_e_pair {ι : Type*} {s : ℕ} (f : ι→ℝ) (x y : Fin s→ι) :
    tupleWeight (fun n=>e (f n)) x*conj (tupleWeight (fun n=>e (f n)) y)=
      e ((∑ i,f (x i))-(∑ i,f (y i))) := by
  rw [tupleWeight,tupleWeight,prod_e,prod_e,e_mul_conj]

/-- The common linear modulation vanishes after the lower-degree
projection. The only surviving translation term is in degree `r+1`. -/
theorem projectedMoment_translation (r s : ℕ) (hr : 1≤r)
    {ι : Type*} [Fintype ι] (v : ι→ℤ) (c : ℤ) (θ γ : ℝ) :
    projectedMoment r s (fun n=>v n+c)
      (fun n=>e (θ*((v n+c : ℤ) : ℝ)^(r+2)+γ*((v n+c : ℤ) : ℝ)))=
    projectedMoment r s v
      (fun n=>e (θ*(v n : ℝ)^(r+2)+(r+2 : ℕ)*(c : ℝ)*θ*(v n : ℝ)^(r+1))) := by
  classical
  apply Complex.ofReal_injective
  rw [projectedMoment_gram,projectedMoment_gram]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [tuplePowerVector_translate_eq_iff]
  by_cases he : tuplePowerVector r v x=tuplePowerVector r v y
  · rw [if_pos he,if_pos he,tupleWeight_e_pair,tupleWeight_e_pair]
    congr 1
    have hh := (tuplePowerVector_eq_iff r v x y).mp he
    have htop := powerDifference_translate_two r (fun i=>v (x i)) (fun i=>v (y i)) c hh
    have hlin := lower_power_difference_translate r (fun i=>v (x i)) (fun i=>v (y i)) c hh 1 hr
    have htopR := congrArg (fun z : ℤ=>(z : ℝ)) htop
    have hlinR := congrArg (fun z : ℤ=>(z : ℝ)) hlin
    simp only [powerDifference,wooleyPowerSum,Int.cast_sub,Int.cast_sum,Int.cast_pow,
      Int.cast_mul,Int.cast_natCast,Int.cast_add,pow_one,Int.cast_zero] at htopR hlinR
    simp only [Finset.sum_add_distrib] at hlinR
    simp only [Int.cast_add,Finset.sum_add_distrib,← Finset.mul_sum]
    linear_combination θ*htopR+γ*hlinR
  · rw [if_neg he,if_neg he]

#print axioms tuplePowerVector_translate_eq_iff
#print axioms projectedMoment_translation
end Waring.EndgameCompletion
