import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# A uniform finite elimination bound for plane curves

The matrix below is the coefficient form of a Sylvester matrix. Its
nonvanishing follows from primality and a degree comparison, and a common
point makes its evaluated determinant vanish. Bounding the degrees of its
entries therefore gives an intersection bound independent of coefficients.
-/

noncomputable section
open scoped BigOperators Polynomial Polynomial.Bivariate Matrix
open Polynomial
namespace Waring.SeedCompletionCurveElimination

section CoefficientMatrix
variable {R : Type*} [CommRing R]

def sylvesterColumn (p q : R[X]) (d : ℕ) (j : Fin (d+d)) : R[X] :=
  j.addCases (fun i : Fin d => p*X^(i : ℕ)) (fun i : Fin d => q*X^(i : ℕ))

def coefficientMatrix (p q : R[X]) (d : ℕ) : Matrix (Fin (d+d)) (Fin (d+d)) R :=
  fun i j => (sylvesterColumn p q d j).coeff i

theorem sylvesterColumn_natDegree_lt (p q : R[X]) (d : ℕ)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (j : Fin (d+d)) :
    (sylvesterColumn p q d j).natDegree < d+d := by
  induction j using Fin.addCases with
  | left i =>
      simp only [sylvesterColumn,Fin.addCases_left]
      exact (natDegree_mul_le.trans (Nat.add_le_add hp (natDegree_X_pow_le _))).trans_lt
        (Nat.add_lt_add_left i.isLt d)
  | right i =>
      simp only [sylvesterColumn,Fin.addCases_right]
      exact (natDegree_mul_le.trans (Nat.add_le_add hq (natDegree_X_pow_le _))).trans_lt
        (Nat.add_lt_add_left i.isLt d)

theorem combination_identity [DecidableEq R] (p q : R[X]) (d : ℕ) (v : Fin (d+d) → R) :
    (∑ j, C (v j)*sylvesterColumn p q d j) =
      p*ofFn d (fun i => v (Fin.castAdd d i)) +
      q*ofFn d (fun i => v (Fin.natAdd d i)) := by
  classical
  rw [Fin.sum_univ_add]
  simp only [sylvesterColumn,Fin.addCases_left,Fin.addCases_right,
    ofFn_eq_sum_monomial,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    rw [← C_mul_X_pow_eq_monomial] <;> ring

theorem combination_coeff (p q : R[X]) (d : ℕ) (v : Fin (d+d) → R)
    (i : Fin (d+d)) :
    (∑ j, C (v j)*sylvesterColumn p q d j).coeff i =
      (coefficientMatrix p q d *ᵥ v) i := by
  classical
  simp only [finset_sum_coeff,coeff_C_mul,Matrix.mulVec,dotProduct,coefficientMatrix]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem combination_eq_zero_of_mulVec_eq_zero (p q : R[X]) (d : ℕ)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d)
    (v : Fin (d+d) → R) (hv : coefficientMatrix p q d *ᵥ v = 0) :
    (∑ j, C (v j)*sylvesterColumn p q d j) = 0 := by
  classical
  ext i
  by_cases hi : i < d+d
  · have h := combination_coeff p q d v ⟨i,hi⟩
    simpa only [hv,Pi.zero_apply,coeff_zero] using h
  · rw [finset_sum_coeff,coeff_zero]
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_C_mul,coeff_eq_zero_of_natDegree_lt
      ((sylvesterColumn_natDegree_lt p q d hp hq j).trans_le (Nat.le_of_not_gt hi)),mul_zero]

variable [IsDomain R]

/-- Nonvanishing over an arbitrary integral domain; only the literal prime
polynomial and degree conditions are used. -/
theorem coefficientMatrix_det_ne_zero (p q : R[X]) (d : ℕ) (hd : 0 < d)
    (hp : Prime p) (hpdeg : p.natDegree=d) (hqdeg : q.natDegree=d)
    (hpq : ¬ p ∣ q) :
    (coefficientMatrix p q d).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v,hv,hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hpoly := combination_eq_zero_of_mulVec_eq_zero p q d hpdeg.le hqdeg.le v hMv
  rw [combination_identity] at hpoly
  let A := ofFn d (fun i => v (Fin.castAdd d i))
  let B := ofFn d (fun i => v (Fin.natAdd d i))
  change p*A+q*B=0 at hpoly
  have hpB : p ∣ q*B := by
    refine ⟨-A,?_⟩
    linear_combination hpoly
  have hBdiv : p ∣ B := (hp.dvd_or_dvd hpB).resolve_left hpq
  have hB : B=0 := by
    by_contra hB0
    have hdeg := natDegree_le_of_dvd hBdiv hB0
    have hlt : B.natDegree < d := ofFn_natDegree_lt hd _
    omega
  have hA : A=0 := by
    rw [hB,mul_zero,add_zero,mul_eq_zero] at hpoly
    exact hpoly.resolve_left hp.ne_zero
  apply hv
  funext j
  induction j using Fin.addCases with
  | left i =>
      have hh := congrArg (fun f : R[X] => f.coeff (i : ℕ)) hA
      simpa only [A,ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero] using hh
  | right i =>
      have hh := congrArg (fun f : R[X] => f.coeff (i : ℕ)) hB
      simpa only [B,ofFn_coeff_eq_val_of_lt _ i.isLt,coeff_zero] using hh

/-- A common root gives an explicit nonzero left-kernel vector. -/
theorem coefficientMatrix_det_eq_zero_of_common_root (p q : R[X]) (d : ℕ)
    (hd : 0 < d) (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (y : R) (hp : p.eval y=0) (hq : q.eval y=0) :
    (coefficientMatrix p q d).det = 0 := by
  classical
  apply Matrix.exists_vecMul_eq_zero_iff.mp
  refine ⟨fun i : Fin (d+d) => y^(i : ℕ),?_,?_⟩
  · intro hz
    have h := congrFun hz ⟨0,by omega⟩
    simpa using h
  · funext j
    have heval : (sylvesterColumn p q d j).eval y=0 := by
      induction j using Fin.addCases with
      | left i => simp only [sylvesterColumn,Fin.addCases_left,eval_mul,eval_pow,eval_X,hp,zero_mul]
      | right i => simp only [sylvesterColumn,Fin.addCases_right,eval_mul,eval_pow,eval_X,hq,zero_mul]
    have hsum := eval_eq_sum_range'
      (sylvesterColumn_natDegree_lt p q d hpdeg hqdeg j) y
    rw [heval] at hsum
    simpa only [Matrix.vecMul,dotProduct,coefficientMatrix,
      ← Fin.sum_univ_eq_sum_range,mul_comm,Pi.zero_apply] using hsum.symm

/-- Coefficient specialization commutes with this exact finite matrix. -/
theorem coefficientMatrix_map {S : Type*} [CommRing S]
    (φ : R →+* S) (p q : R[X]) (d : ℕ) :
    (coefficientMatrix p q d).map φ = coefficientMatrix (p.map φ) (q.map φ) d := by
  ext i j
  induction j using Fin.addCases with
  | left j =>
      simp only [coefficientMatrix,Matrix.map_apply,sylvesterColumn,Fin.addCases_left]
      rw [← coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
  | right j =>
      simp only [coefficientMatrix,Matrix.map_apply,sylvesterColumn,Fin.addCases_right]
      rw [← coeff_map,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]

#print axioms coefficientMatrix_det_ne_zero
#print axioms coefficientMatrix_det_eq_zero_of_common_root
end CoefficientMatrix
section PlaneElimination
variable {K : Type*} [CommRing K]

/-- A coefficient-independent degree bound for a determinant. -/
theorem matrix_det_natDegree_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K[X]) (D : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ D) :
    M.det.natDegree ≤ Fintype.card ι*D := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  have hsign : (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree =
      (∏ i, M (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h,one_smul]
    · rw [h,Units.neg_smul,one_smul,natDegree_neg]
  rw [hsign]
  calc
    (∏ i, M (σ i) i).natDegree ≤ ∑ i, (M (σ i) i).natDegree :=
      natDegree_prod_le _ _
    _ ≤ ∑ _i : ι, D := Finset.sum_le_sum (fun i _ => hM (σ i) i)
    _ = _ := by simp

def eliminationPolynomial (p q : K[X][Y]) (d : ℕ) : K[X] :=
  (coefficientMatrix p q d).det

/-- If both coordinate degrees are bounded, the elimination polynomial has
uniformly bounded degree; its coefficients may have arbitrary size. -/
theorem eliminationPolynomial_natDegree_le (p q : K[X][Y]) (d D : ℕ)
    (hp : ∀ n, (p.coeff n).natDegree ≤ D)
    (hq : ∀ n, (q.coeff n).natDegree ≤ D) :
    (eliminationPolynomial p q d).natDegree ≤ (d+d)*D := by
  classical
  apply (matrix_det_natDegree_le _ D ?_).trans_eq (by simp)
  intro i j
  induction j using Fin.addCases with
  | left j =>
      simp only [coefficientMatrix,sylvesterColumn,Fin.addCases_left,coeff_mul_X_pow']
      split_ifs
      · exact hp _
      · simp
  | right j =>
      simp only [coefficientMatrix,sylvesterColumn,Fin.addCases_right,coeff_mul_X_pow']
      split_ifs
      · exact hq _
      · simp

variable [IsDomain K]

/-- The elimination polynomial vanishes at the first coordinate of every
literal common point. -/
theorem eliminationPolynomial_eval_zero (p q : K[X][Y]) (d : ℕ) (hd : 0 < d)
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (x y : K) (hp : p.evalEval x y=0) (hq : q.evalEval x y=0) :
    (eliminationPolynomial p q d).eval x=0 := by
  change (evalRingHom x) ((coefficientMatrix p q d).det)=0
  rw [RingHom.map_det]
  change ((coefficientMatrix p q d).map (evalRingHom x)).det=0
  rw [coefficientMatrix_map]
  apply coefficientMatrix_det_eq_zero_of_common_root _ _ d hd
    ((natDegree_map_le).trans hpdeg) ((natDegree_map_le).trans hqdeg) y
  · simpa only [map_evalRingHom_eval] using hp
  · simpa only [map_evalRingHom_eval] using hq

/-- A finite common-point set with distinct first coordinates is bounded
solely by the two polynomial degrees. This is the exact intersection form
needed for monotone lattice-point sequences. -/
theorem common_points_card_le (p q : K[X][Y]) (d D : ℕ) (hd : 0 < d)
    (hp : Prime p) (hpdeg : p.natDegree=d) (hqdeg : q.natDegree=d)
    (hpq : ¬p ∣ q)
    (hpX : ∀ n, (p.coeff n).natDegree ≤ D)
    (hqX : ∀ n, (q.coeff n).natDegree ≤ D)
    (S : Finset (K×K))
    (hpoints : ∀ z ∈ S, p.evalEval z.1 z.2=0 ∧ q.evalEval z.1 z.2=0)
    (hinj : Set.InjOn Prod.fst (↑S : Set (K×K))) :
    S.card ≤ (d+d)*D := by
  classical
  have hres : eliminationPolynomial p q d ≠ 0 :=
    coefficientMatrix_det_ne_zero p q d hd hp hpdeg hqdeg hpq
  have hroots : (S.image Prod.fst).val ⊆ (eliminationPolynomial p q d).roots := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (mem_roots hres).mpr
      (eliminationPolynomial_eval_zero p q d hd hpdeg.le hqdeg.le _ _
        (hpoints z hz).1 (hpoints z hz).2)
  calc
    S.card = (S.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (eliminationPolynomial p q d).natDegree := card_le_degree_of_subset_roots hroots
    _ ≤ (d+d)*D := eliminationPolynomial_natDegree_le p q d D hpX hqX

#print axioms eliminationPolynomial_eval_zero
#print axioms common_points_card_le
end PlaneElimination
end Waring.SeedCompletionCurveElimination
