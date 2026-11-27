import Waring.EvenMoments
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.Field.ZMod

/-! # The finite Newton collision bound used in Mordell's estimate

Equal power sums through degree d determine the elementary symmetric
functions, provided 1,...,d are nonzero in the field. Every coordinate of
one tuple is then a root of the other's split polynomial. The deliberately
coarse d^d bound is uniform and sufficient for the complete-sum estimate.
-/

noncomputable section
open scoped BigOperators Polynomial
namespace Waring.FiniteFieldMordell

section Field
variable {K : Type*} [Field K] {d : ℕ}

def esymmValue (x : Fin d → K) (j : ℕ) : K :=
  MvPolynomial.aeval x (MvPolynomial.esymm (Fin d) K j)

theorem newton_value (x : Fin d → K) (j : ℕ) :
    (j : K)*esymmValue x j=(-1 : K)^(j+1)*
      ∑ a ∈ (Finset.antidiagonal j).filter (fun a => a.1<j),
        (-1 : K)^a.1*esymmValue x a.1*(∑ i,(x i)^a.2) := by
  have h := congrArg (MvPolynomial.aeval x) (MvPolynomial.mul_esymm_eq_sum (Fin d) K j)
  simpa [esymmValue,MvPolynomial.psum] using h

theorem esymmValue_eq_of_power_sums {x y : Fin d → K}
    (hchar : ∀ j : ℕ,1 ≤ j → j ≤ d → (j : K) ≠ 0)
    (hpower : ∀ j : ℕ,1 ≤ j → j ≤ d → (∑ i,(x i)^j)=∑ i,(y i)^j)
    (j : ℕ) (hj : j ≤ d) : esymmValue x j=esymmValue y j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
      by_cases hj0 : j=0
      · subst j
        simp [esymmValue,MvPolynomial.esymm_zero]
      apply mul_left_cancel₀ (hchar j (by omega) hj)
      rw [newton_value,newton_value]
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      obtain ⟨hanti,halt⟩ := Finset.mem_filter.mp ha
      have heq := Finset.mem_antidiagonal.mp hanti
      rw [ih a.1 halt (by omega),hpower a.2 (by omega) (by omega)]

def rootPolynomial (x : Fin d → K) : K[X] := ∏ i, (Polynomial.X-Polynomial.C (x i))

theorem rootPolynomial_eq_of_power_sums {x y : Fin d → K}
    (hchar : ∀ j : ℕ,1 ≤ j → j ≤ d → (j : K) ≠ 0)
    (hpower : ∀ j : ℕ,1 ≤ j → j ≤ d → (∑ i,(x i)^j)=∑ i,(y i)^j) :
    rootPolynomial x=rootPolynomial y := by
  let sx := Finset.univ.val.map x
  let sy := Finset.univ.val.map y
  have hx : rootPolynomial x=(sx.map (fun z => Polynomial.X-Polynomial.C z)).prod := by
    simp only [rootPolynomial,sx,Multiset.map_map,Finset.prod]
    rfl
  have hy : rootPolynomial y=(sy.map (fun z => Polynomial.X-Polynomial.C z)).prod := by
    simp only [rootPolynomial,sy,Multiset.map_map,Finset.prod]
    rfl
  have hcardx : sx.card=d := by simp [sx]
  have hcardy : sy.card=d := by simp [sy]
  rw [hx,hy,Multiset.prod_X_sub_X_eq_sum_esymm,Multiset.prod_X_sub_X_eq_sum_esymm,hcardx,hcardy]
  apply Finset.sum_congr rfl
  intro j hj
  have he : sx.esymm j=sy.esymm j := by
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin d) K j x,
      ← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin d) K j y]
    exact esymmValue_eq_of_power_sums hchar hpower j (by have := Finset.mem_range.mp hj; omega)
  rw [he]

theorem coordinate_mem_of_power_sums {x y : Fin d → K}
    (hchar : ∀ j : ℕ,1 ≤ j → j ≤ d → (j : K) ≠ 0)
    (hpower : ∀ j : ℕ,1 ≤ j → j ≤ d → (∑ i,(x i)^j)=∑ i,(y i)^j)
    (j : Fin d) : ∃ i : Fin d,x i=y j := by
  classical
  have hy : (rootPolynomial y).eval (y j)=0 := by
    rw [rootPolynomial,Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  rw [← rootPolynomial_eq_of_power_sums hchar hpower] at hy
  rw [rootPolynomial,Polynomial.eval_prod] at hy
  obtain ⟨i,_,hi⟩ := Finset.prod_eq_zero_iff.mp hy
  exact ⟨i,(sub_eq_zero.mp (by simpa using hi)).symm⟩

variable [Fintype K] [DecidableEq K]

def powerSumFiber (x : Fin d → K) : Finset (Fin d → K) :=
  Finset.univ.filter (fun y => ∀ j : ℕ,1 ≤ j → j ≤ d →
    (∑ i,(x i)^j)=∑ i,(y i)^j)

theorem powerSumFiber_card_le (x : Fin d → K)
    (hchar : ∀ j : ℕ,1 ≤ j → j ≤ d → (j : K) ≠ 0) :
    (powerSumFiber x).card ≤ d^d := by
  classical
  have hsub : powerSumFiber x ⊆ finiteTuples (Finset.univ.image x) d := by
    intro y hy
    apply Fintype.mem_piFinset.mpr
    intro j
    obtain ⟨i,hi⟩ := coordinate_mem_of_power_sums hchar (Finset.mem_filter.mp hy).2 j
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
  calc
    _ ≤ (finiteTuples (Finset.univ.image x) d).card := Finset.card_le_card hsub
    _ = (Finset.univ.image x).card^d := by simp [finiteTuples,Fintype.card_piFinset]
    _ ≤ d^d := Nat.pow_le_pow_left (by simpa using Finset.card_image_le (s := Finset.univ) (f := x)) d

end Field

theorem zmod_powerSumFiber_card_le {p d : ℕ} [Fact p.Prime] (hdp : d<p)
    (x : Fin d → ZMod p) : (powerSumFiber x).card ≤ d^d := by
  apply powerSumFiber_card_le
  intro j hj hjd hz
  have hdiv := (ZMod.natCast_eq_zero_iff j p).mp hz
  have hpj := Nat.le_of_dvd (by omega : 0 < j) hdiv
  omega

#print axioms zmod_powerSumFiber_card_le
end Waring.FiniteFieldMordell
