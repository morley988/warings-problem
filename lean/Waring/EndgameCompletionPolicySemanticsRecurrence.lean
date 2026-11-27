import Waring.EndgameCompletionPolicySemanticsChecked

/-! # Real prefix parameters and the exact stored backward recurrence -/

noncomputable section
open scoped BigOperators
namespace Waring.Certificate
open PolicyCompletionMajorPowerRanges

def prefixPhi (p : Policy) (j : ℕ) (i : Fin j) : ℝ := (p.phi[i.val]! : ℝ)

theorem prefixPhi_full (p : Policy) : prefixPhi p p.phi.size=phiReal p := rfl

theorem prefixTotal_succ {p : Policy} {j : ℕ} (hj : j<p.phi.size) :
    prefixTotal p (j+1)=prefixTotal p j+p.phi[j]! := by
  unfold prefixTotal
  rw [← List.sum_eq_foldl,← List.sum_eq_foldl]
  have H := List.sum_take_succ p.phi.toList j (by simpa using hj)
  simpa only [Array.getElem_toList,getElem!_pos p.phi j hj] using H

theorem prefixTotal_cast_eq_total {p : Policy} {j : ℕ} (hj : j≤p.phi.size) :
    (prefixTotal p j : ℝ)=total (prefixPhi p j) := by
  have he : List.ofFn (fun i : Fin j => p.phi[i.val]!)=p.phi.toList.take j := by
    apply List.ext_getElem
    · simp [Nat.min_eq_left hj]
    · intro i hi hi'
      have hij : i<j := by simpa using hi
      have hip : i<p.phi.size := hij.trans_le hj
      simp only [List.getElem_ofFn,List.getElem_take,Array.getElem_toList]
      exact getElem!_pos p.phi i hip
  unfold prefixTotal
  rw [← List.sum_eq_foldl,← he,Fin.sum_ofFn]
  simp only [Rat.cast_sum,total,prefixPhi]

theorem prefixLength_cast {p : Policy} {j : ℕ} (hj : j≤p.phi.size) :
    (prefixLength p j : ℝ)=1-total (prefixPhi p j) := by
  simp only [prefixLength,Rat.cast_sub,Rat.cast_one,prefixTotal_cast_eq_total hj]

theorem prefixShift_cast (k : ℕ) {p : Policy} {j : ℕ} (hj : j≤p.phi.size) :
    (prefixShift k p j : ℝ)=(j : ℝ)-(k : ℝ)*total (prefixPhi p j) := by
  simp only [prefixShift,q,Rat.cast_sub,Rat.cast_mul,Rat.cast_natCast,
    prefixTotal_cast_eq_total hj]

theorem prefixTotal_cast_succ {p : Policy} {j : ℕ} (hj : j<p.phi.size) :
    (prefixTotal p (j+1) : ℝ)=total (prefixPhi p j)+(p.phi[j]! : ℝ) := by
  rw [prefixTotal_succ hj,Rat.cast_add,prefixTotal_cast_eq_total hj.le]

def prefixAmplitude (k : ℕ) (p : Policy) (j : ℕ) : ℝ :=
  (j : ℝ)+(1-(k : ℝ))*total (prefixPhi p j)

theorem recurrenceRow_prefactor_cast (k : ℕ) (curve : Curve) {p : Policy} {j : ℕ}
    (hj : j<p.phi.size) :
    ((recurrenceRow k curve p j).1 : ℝ)=
      (((moment curve (2*(2*p.path[j-1]!-p.path[j]!))).getD 0 : ℝ)*
          (1-total (prefixPhi p j))+prefixAmplitude k p j+
        (((2*p.path[j]! : ℕ) : ℝ)-1)*(p.phi[j]! : ℝ))/2 := by
  simp only [recurrenceRow,Rat.cast_add,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,
    Rat.cast_ofNat,Rat.cast_one,q,Rat.cast_natCast,prefixLength_cast hj.le,
    prefixShift_cast k hj.le,prefixTotal_cast_eq_total hj.le,prefixAmplitude]
  ring

theorem recurrenceRow_diagonal_cast (k : ℕ) (curve : Curve) {p : Policy} {j : ℕ}
    (hj : j<p.phi.size) :
    ((recurrenceRow k curve p j).2 : ℝ)=
      prefixAmplitude k p j+1+(p.phi[j]! : ℝ)+
        (1-total (prefixPhi p j)-(p.phi[j]! : ℝ))*
          ((moment curve (2*p.path[j]!)).getD 0 : ℝ) := by
  simp only [recurrenceRow,Rat.cast_add,Rat.cast_mul,Rat.cast_one,
    prefixShift_cast k hj.le,prefixTotal_cast_succ hj,prefixLength,Rat.cast_sub,
    prefixAmplitude]
  ring

theorem firstOffset_cast (p : Policy) :
    (firstOffset p : ℝ)=(((2*p.halfOrder : ℕ) : ℝ)-3)*(p.phi[0]! : ℝ) := by
  simp only [firstOffset,Rat.cast_mul,Rat.cast_sub,Rat.cast_ofNat,q,Rat.cast_natCast]

theorem firstDiagonal_cast (curve : Curve) {p : Policy} (hp : 0<p.phi.size) :
    (firstDiagonal curve p : ℝ)=1+(p.phi[0]! : ℝ)+
      (1-(p.phi[0]! : ℝ))*((moment curve (2*(p.halfOrder-1))).getD 0 : ℝ) := by
  have hzero : prefixTotal p 0=0 := rfl
  have hone := prefixTotal_succ hp
  rw [hzero,zero_add] at hone
  simp only [firstDiagonal,Rat.cast_add,Rat.cast_mul,Rat.cast_one,prefixLength,
    hone,Rat.cast_sub]
  ring

#print axioms prefixTotal_cast_eq_total
#print axioms recurrenceRow_prefactor_cast
#print axioms recurrenceRow_diagonal_cast
end Waring.Certificate
