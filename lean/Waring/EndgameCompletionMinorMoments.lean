import Waring.External.GafniTao.FordVinogradovIntegral
import Waring.External.GafniTao.WooleyTranslationDilation
import Waring.FourierCompletionMoments

/-!
# Exact projected polynomial moments

Finite weighted Fourier orthogonality and translation algebra used in the
ordinary minor-arc transport. All moments are literal normalized-Haar
integrals of finite sums.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace Waring.EndgameCompletion

abbrev unitTorusMeasure (r : ℕ) : Measure (UnitAddTorus (Fin r)) :=
  Measure.pi (fun _ : Fin r=>AddCircle.haarAddCircle)

def finiteTorusSum {ι : Type*} [Fintype ι] {r : ℕ}
    (v : ι→Fin r→ℤ) (w : ι→ℂ) (α : UnitAddTorus (Fin r)) : ℂ :=
  ∑ i,w i*UnitAddTorus.mFourier (v i) α

theorem continuous_finiteTorusSum {ι : Type*} [Fintype ι] {r : ℕ}
    (v : ι→Fin r→ℤ) (w : ι→ℂ) : Continuous (finiteTorusSum v w) :=
  continuous_finset_sum _ (fun i _=>continuous_const.mul
    (UnitAddTorus.mFourier (v i)).continuous)

theorem integrable_continuous_torus {r : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : UnitAddTorus (Fin r)→E)
    (hf : Continuous f) : Integrable f (unitTorusMeasure r) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem finiteTorusSum_norm_sq_expand {ι : Type*} [Fintype ι] {r : ℕ}
    (v : ι→Fin r→ℤ) (w : ι→ℂ) (α : UnitAddTorus (Fin r)) :
    ((‖finiteTorusSum v w α‖^2 : ℝ) : ℂ)=
      ∑ i,∑ j,(w i*conj (w j))*UnitAddTorus.mFourier (v i-v j) α := by
  classical
  rw [Complex.ofReal_pow,← Complex.mul_conj']
  simp only [finiteTorusSum,map_sum,map_mul,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sub_eq_add_neg,UnitAddTorus.mFourier_add,UnitAddTorus.mFourier_neg]
  ring

theorem finiteTorusSum_gram {ι : Type*} [Fintype ι] {r : ℕ}
    (v : ι→Fin r→ℤ) (w : ι→ℂ) :
    ((∫ α,‖finiteTorusSum v w α‖^2 ∂unitTorusMeasure r : ℝ) : ℂ)=
      ∑ i,∑ j,if v i=v j then w i*conj (w j) else 0 := by
  classical
  have hi (i j : ι) : Integrable
      (fun α=>(w i*conj (w j))*UnitAddTorus.mFourier (v i-v j) α)
      (unitTorusMeasure r) :=
    integrable_continuous_torus _
      (continuous_const.mul (UnitAddTorus.mFourier (v i-v j)).continuous)
  have hcast : (∫ α,((‖finiteTorusSum v w α‖^2 : ℝ) : ℂ) ∂unitTorusMeasure r)=
      ((∫ α,‖finiteTorusSum v w α‖^2 ∂unitTorusMeasure r : ℝ) : ℂ) := integral_ofReal
  rw [← hcast]
  simp_rw [finiteTorusSum_norm_sq_expand]
  rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _=>hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,GafniTao.ford_integral_mFourier_pi_haar_eq]
  simp only [sub_eq_zero]
  split_ifs <;> simp

theorem finiteTorusSum_fiber_norm_sq {ι : Type*} [Fintype ι] {r : ℕ}
    (v : ι→Fin r→ℤ) (w : ι→ℂ) (A : Finset (Fin r→ℤ))
    (hA : ∀ i,v i∈A) :
    (∫ α,‖finiteTorusSum v w α‖^2 ∂unitTorusMeasure r)=
      ∑ a∈A,‖∑ i∈Finset.univ.filter (fun i=>v i=a),w i‖^2 := by
  classical
  apply Complex.ofReal_injective
  rw [finiteTorusSum_gram,Complex.ofReal_sum]
  symm
  calc
    _ = ∑ a∈A,∑ i∈Finset.univ.filter (fun i=>v i=a),
          ∑ j∈Finset.univ.filter (fun j=>v j=a),w i*conj (w j) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Complex.ofReal_pow,← Complex.mul_conj',map_sum,Finset.sum_mul_sum]
    _ = ∑ a∈A,∑ i∈Finset.univ.filter (fun i=>v i=a),
          ∑ j,if v i=v j then w i*conj (w j) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i hi
      have hv := (Finset.mem_filter.mp hi).2
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      simp only [hv,eq_comm]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun i _=>hA i) _

/-- Finite Cauchy followed by exact lower-frequency orthogonality. -/
theorem norm_sum_sq_le_projected {ι : Type*} [Fintype ι] {r : ℕ}
    (v : ι→Fin r→ℤ) (w : ι→ℂ) (A : Finset (Fin r→ℤ))
    (hA : ∀ i,v i∈A) :
    ‖∑ i,w i‖^2≤(A.card : ℝ)*
      (∫ α,‖finiteTorusSum v w α‖^2 ∂unitTorusMeasure r) := by
  classical
  let F := fun a=>∑ i∈Finset.univ.filter (fun i=>v i=a),w i
  have he : (∑ a∈A,F a)=∑ i,w i :=
    Finset.sum_fiberwise_of_maps_to (fun i _=>hA i) _
  have hc := Finset.sum_mul_sq_le_sq_mul_sq A (fun _=>(1 : ℝ)) (fun a=>‖F a‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  rw [finiteTorusSum_fiber_norm_sq v w A hA,← he]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hc

def tuplePowerVector {ι : Type*} {s : ℕ} (r : ℕ) (v : ι→ℤ)
    (x : Fin s→ι) : Fin r→ℤ :=
  fun j=>∑ i,(v (x i))^(j.val+1)

def tupleWeight {ι : Type*} {s : ℕ} (w : ι→ℂ) (x : Fin s→ι) : ℂ :=
  ∏ i,w (x i)

def polynomialTorusSum {ι : Type*} [Fintype ι] (r : ℕ)
    (v : ι→ℤ) (w : ι→ℂ) (α : UnitAddTorus (Fin r)) : ℂ :=
  finiteTorusSum (fun n j=>(v n)^(j.val+1)) w α

theorem polynomialTorusSum_pow {ι : Type*} [Fintype ι]
    (r s : ℕ) (v : ι→ℤ) (w : ι→ℂ) (α : UnitAddTorus (Fin r)) :
    polynomialTorusSum r v w α^s=
      finiteTorusSum (tuplePowerVector (s := s) r v) (tupleWeight w) α := by
  classical
  unfold polynomialTorusSum finiteTorusSum
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]
  congr 1
  have hv : tuplePowerVector r v x=∑ i : Fin s,fun j : Fin r=>(v (x i))^(j.val+1) := by
    ext j
    simp [tuplePowerVector]
  rw [hv]
  induction (Finset.univ : Finset (Fin s)) using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,UnitAddTorus.mFourier_add,ih]

def projectedMoment {ι : Type*} [Fintype ι] (r s : ℕ)
    (v : ι→ℤ) (w : ι→ℂ) : ℝ :=
  ∫ α,‖polynomialTorusSum r v w α‖^(2*s) ∂unitTorusMeasure r

theorem projectedMoment_nonneg {ι : Type*} [Fintype ι] (r s : ℕ)
    (v : ι→ℤ) (w : ι→ℂ) : 0≤projectedMoment r s v w :=
  integral_nonneg (fun _=>pow_nonneg (norm_nonneg _) _)

theorem projectedMoment_gram {ι : Type*} [Fintype ι] (r s : ℕ)
    (v : ι→ℤ) (w : ι→ℂ) :
    (projectedMoment r s v w : ℂ)=
      ∑ x : Fin s→ι,∑ y : Fin s→ι,
        if tuplePowerVector r v x=tuplePowerVector r v y
        then tupleWeight w x*conj (tupleWeight w y) else 0 := by
  rw [projectedMoment]
  have he (α : UnitAddTorus (Fin r)) :
      ‖polynomialTorusSum r v w α‖^(2*s)=
        ‖finiteTorusSum (tuplePowerVector (s := s) r v) (tupleWeight w) α‖^2 := by
    rw [← polynomialTorusSum_pow,norm_pow,← pow_mul]
    congr 1
    omega
  simp_rw [he]
  exact finiteTorusSum_gram _ _

theorem norm_sum_pow_le_projected {ι : Type*} [Fintype ι] (r s : ℕ)
    (v : ι→ℤ) (w : ι→ℂ) (A : Finset (Fin r→ℤ))
    (hA : ∀ x : Fin s→ι,tuplePowerVector r v x∈A) :
    ‖∑ i,w i‖^(2*s)≤(A.card : ℝ)*projectedMoment r s v w := by
  have hh := norm_sum_sq_le_projected (tuplePowerVector (s := s) r v)
    (tupleWeight w) A hA
  have he : (∑ x : Fin s→ι,tupleWeight w x)=(∑ i,w i)^s := by
    rw [Fintype.sum_pow]
    rfl
  rw [he,norm_pow,← pow_mul] at hh
  have hpoint (α : UnitAddTorus (Fin r)) :
      ‖finiteTorusSum (tuplePowerVector (s := s) r v) (tupleWeight w) α‖^2=
        ‖polynomialTorusSum r v w α‖^(2*s) := by
    rw [← polynomialTorusSum_pow,norm_pow,← pow_mul]
    congr 1
    omega
  simpa only [mul_comm s 2,hpoint] using hh

def lowerPowerBox (r s N : ℕ) : Finset (Fin r→ℤ) :=
  Fintype.piFinset (fun j : Fin r=>Finset.Icc 0 ((s*N^(j.val+1) : ℕ) : ℤ))

theorem tuplePowerVector_mem_box {ι : Type*} {s : ℕ} (r N : ℕ) (v : ι→ℤ)
    (hv0 : ∀ n,0≤v n) (hvN : ∀ n,v n≤N) (x : Fin s→ι) :
    tuplePowerVector r v x∈lowerPowerBox r s N := by
  classical
  rw [lowerPowerBox,Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_Icc]
  constructor
  · exact Finset.sum_nonneg (fun i _=>pow_nonneg (hv0 (x i)) _)
  · calc
      _ ≤ ∑ _i : Fin s,(N : ℤ)^(j.val+1) :=
        Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (hv0 (x i)) (hvN (x i)) _)
      _ = _ := by simp

theorem lowerPowerBox_card (r s N : ℕ) :
    (lowerPowerBox r s N).card=∏ j : Fin r,(s*N^(j.val+1)+1) := by
  rw [lowerPowerBox,Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Int.card_Icc,sub_zero]
  norm_cast

theorem lowerPowerBox_card_le (r s N : ℕ) (hN : 1≤N) :
    ((lowerPowerBox r s N).card : ℝ)≤
      ((s : ℝ)+1)^r*(N : ℝ)^(∑ j : Fin r,(j.val+1)) := by
  rw [lowerPowerBox_card,Nat.cast_prod]
  calc
    _ ≤ ∏ j : Fin r,((s : ℝ)+1)*(N : ℝ)^(j.val+1) := by
      apply Finset.prod_le_prod (fun j _=>by positivity)
      intro j _
      push_cast
      have hp : (1 : ℝ)≤(N : ℝ)^(j.val+1) := one_le_pow₀ (by exact_mod_cast hN)
      nlinarith
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum]

/-- The initial lower-coefficient projection, with its exact polynomial
cardinality loss. -/
theorem polynomial_lower_projection {ι : Type*} [Fintype ι] (r s N : ℕ)
    (hN : 1≤N) (v : ι→ℤ) (w : ι→ℂ)
    (hv0 : ∀ n,0≤v n) (hvN : ∀ n,v n≤N) :
    ‖∑ i,w i‖^(2*s)≤
      (((s : ℝ)+1)^r*(N : ℝ)^(∑ j : Fin r,(j.val+1)))*projectedMoment r s v w := by
  exact (norm_sum_pow_le_projected r s v w (lowerPowerBox r s N)
    (tuplePowerVector_mem_box r N v hv0 hvN)).trans
      (mul_le_mul_of_nonneg_right (lowerPowerBox_card_le r s N hN)
        (projectedMoment_nonneg r s v w))

#print axioms finiteTorusSum_gram
#print axioms projectedMoment_gram
#print axioms polynomial_lower_projection
end Waring.EndgameCompletion
