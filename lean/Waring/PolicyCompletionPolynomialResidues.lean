import Waring.PolicyCompletionPolynomialContent
import Waring.EndgameCompletionCRT

/-! # Exact residue-class and modulus reduction for polynomial phases -/

noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionPolynomialResidues
open Polynomial EndgameCompletion PolicyCompletionPolynomialStationary
  PolicyCompletionPolynomialBranch

def integerPolynomialSum (q : ℕ) [NeZero q] (f : Polynomial ℤ) : ℂ :=
  completePolynomialSum q (f.map (Int.castRingHom (ZMod q)))

def residuePolynomialSum (p m r : ℕ) [NeZero (p^m)] (f : Polynomial ℤ) : ℂ :=
  ∑ y ∈ Finset.range (p^(m-1)),
    ZMod.stdAddChar ((f.eval ((r : ℤ)+(p : ℤ)*y) : ℤ) : ZMod (p^m))

theorem integerPolynomialSum_eq_range (q : ℕ) [NeZero q] (f : Polynomial ℤ) :
    integerPolynomialSum q f=∑ y ∈ Finset.range q,
      ZMod.stdAddChar ((f.eval (y : ℤ) : ℤ) : ZMod q) := by
  unfold integerPolynomialSum completePolynomialSum
  rw [sum_zmod_eq_sum_range]
  apply Finset.sum_congr rfl
  intro y _
  rw [Polynomial.eval_natCast_map]
  rfl

/-- Every residue in one class has a unique canonical affine parameter. -/
theorem sum_zmod_filter_residue (q p M r : ℕ) [NeZero q] (hp : 0 < p)
    (hq : q=p*M) (hr : r < p) (F : ZMod q → ℂ) :
    (∑ x ∈ (Finset.univ : Finset (ZMod q)).filter (fun x => x.val%p=r),F x)=
      ∑ y ∈ Finset.range M,F ((r+p*y : ℕ) : ZMod q) := by
  have hbound {y : ℕ} (hy : y ∈ Finset.range M) : r+p*y < q := by
    have hy' : y+1 ≤ M := Finset.mem_range.mp hy
    have hm := Nat.mul_le_mul_left p hy'
    rw [hq]
    nlinarith
  symm
  apply Finset.sum_bij (fun y _ => ((r+p*y : ℕ) : ZMod q))
  · intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [ZMod.val_natCast_of_lt (hbound hy)]
    simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
  · intro y hy z hz he
    have hh := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (hbound hy),ZMod.val_natCast_of_lt (hbound hz)] at hh
    exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel hh)
  · intro x hx
    have hxr := (Finset.mem_filter.mp hx).2
    have he : r+p*(x.val/p)=x.val := by
      simpa only [hxr] using Nat.mod_add_div x.val p
    refine ⟨x.val/p,Finset.mem_range.mpr ?_,?_⟩
    · apply (Nat.div_lt_iff_lt_mul hp).mpr
      rw [Nat.mul_comm M p,← hq]
      exact ZMod.val_lt x
    · rw [he,ZMod.natCast_zmod_val]
  · intro y _
    rfl

/-- The complete sum is the sum of its literal p residue branches. -/
theorem integerPolynomialSum_eq_residue_sum {p : ℕ} [Fact p.Prime]
    (m : ℕ) (hm : 1 ≤ m) (f : Polynomial ℤ) :
    integerPolynomialSum (p^m) f=
      ∑ r ∈ Finset.range p,residuePolynomialSum p m r f := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hmap : ∀ x ∈ (Finset.univ : Finset (ZMod (p^m))),x.val%p ∈ Finset.range p := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  unfold integerPolynomialSum completePolynomialSum
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro r hr
  rw [sum_zmod_filter_residue (p^m) p (p^(m-1)) r hp
    (by rw [← pow_succ',Nat.sub_add_cancel hm]) (Finset.mem_range.mp hr)]
  unfold residuePolynomialSum
  apply Finset.sum_congr rfl
  intro y hy
  rw [Polynomial.eval_natCast_map]
  congr 1

theorem stdAddChar_primepower_factor {p : ℕ} [Fact p.Prime]
    (m σ : ℕ) (hσ : σ ≤ m) (a : ℤ) :
    ZMod.stdAddChar (((p : ℤ)^σ*a : ℤ) : ZMod (p^m))=
      ZMod.stdAddChar (a : ZMod (p^(m-σ))) := by
  rw [ZMod.stdAddChar_coe,ZMod.stdAddChar_coe]
  congr 1
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  push_cast
  rw [show (p : ℂ)^m=p^σ*p^(m-σ) by rw [← pow_add,Nat.add_sub_of_le hσ]]
  field_simp

/-- Removing branch content also removes exactly sigma-1 repeated periods. -/
theorem residuePolynomialSum_eq_reduced {p : ℕ} [Fact p.Prime]
    (m σ r : ℕ) (hσ : 1 ≤ σ) (hσm : σ ≤ m) (f g : Polynomial ℤ)
    (hbranch : shiftedDifference f (p : ℤ) r=C ((p : ℤ)^σ)*g) :
    residuePolynomialSum p m r f=
      ZMod.stdAddChar ((f.eval (r : ℤ) : ℤ) : ZMod (p^m))*
        ((p^(σ-1) : ℕ) : ℂ)*integerPolynomialSum (p^(m-σ)) g := by
  have heval (y : ℕ) : f.eval ((r : ℤ)+(p : ℤ)*y)=
      f.eval (r : ℤ)+(p : ℤ)^σ*g.eval (y : ℤ) := by
    have he := congrArg (fun F : Polynomial ℤ => F.eval (y : ℤ)) hbranch
    simp only [shiftedDifference,Polynomial.eval_sub,Polynomial.eval_comp,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] at he
    rw [add_comm (r : ℤ) ((p : ℤ)*y)]
    linarith
  have hphase (y : ℕ) :
      ZMod.stdAddChar ((f.eval ((r : ℤ)+(p : ℤ)*y) : ℤ) : ZMod (p^m))=
        ZMod.stdAddChar ((f.eval (r : ℤ) : ℤ) : ZMod (p^m))*
          ZMod.stdAddChar ((g.eval (y : ℤ) : ℤ) : ZMod (p^(m-σ))) := by
    rw [heval,Int.cast_add,AddChar.map_add_eq_mul,stdAddChar_primepower_factor m σ hσm]
  have hper : Function.Periodic
      (fun y : ℕ => ZMod.stdAddChar ((g.eval (y : ℤ) : ℤ) : ZMod (p^(m-σ))))
        (p^(m-σ)) := by
    intro y
    change ZMod.stdAddChar ((Int.castRingHom (ZMod (p^(m-σ)))) (g.eval ((y+p^(m-σ) : ℕ) : ℤ))) =
      ZMod.stdAddChar ((Int.castRingHom (ZMod (p^(m-σ)))) (g.eval (y : ℤ)))
    rw [← Polynomial.eval_natCast_map,← Polynomial.eval_natCast_map]
    simp only [Nat.cast_add,ZMod.natCast_self,add_zero]
  unfold residuePolynomialSum
  simp_rw [hphase]
  rw [← Finset.mul_sum]
  have hlen : p^(m-1)=p^(σ-1)*p^(m-σ) := by rw [← pow_add]; congr 1; omega
  rw [hlen,periodic_sum_full_blocks hper,← integerPolynomialSum_eq_range,mul_assoc]

/-- If all branch coefficients vanish at the modulus, the branch is
exactly its constant phase times its cardinality. -/
theorem residuePolynomialSum_eq_constant {p : ℕ} [Fact p.Prime]
    (m σ r : ℕ) (hmσ : m ≤ σ) (f g : Polynomial ℤ)
    (hbranch : shiftedDifference f (p : ℤ) r=C ((p : ℤ)^σ)*g) :
    residuePolynomialSum p m r f=
      ZMod.stdAddChar ((f.eval (r : ℤ) : ℤ) : ZMod (p^m))*((p^(m-1) : ℕ) : ℂ) := by
  have heval (y : ℕ) : f.eval ((r : ℤ)+(p : ℤ)*y)=
      f.eval (r : ℤ)+(p : ℤ)^σ*g.eval (y : ℤ) := by
    have he := congrArg (fun F : Polynomial ℤ => F.eval (y : ℤ)) hbranch
    simp only [shiftedDifference,Polynomial.eval_sub,Polynomial.eval_comp,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X] at he
    rw [add_comm (r : ℤ) ((p : ℤ)*y)]
    linarith
  have hz : (((p : ℤ)^σ : ℤ) : ZMod (p^m))=0 := by
    rw [Int.cast_pow,Int.cast_natCast,← Nat.cast_pow,ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p hmσ
  unfold residuePolynomialSum
  simp_rw [heval,Int.cast_add,Int.cast_mul,hz,zero_mul,add_zero]
  simp [mul_comm]

#print axioms integerPolynomialSum_eq_residue_sum
#print axioms residuePolynomialSum_eq_reduced
#print axioms residuePolynomialSum_eq_constant
end Waring.PolicyCompletionPolynomialResidues
