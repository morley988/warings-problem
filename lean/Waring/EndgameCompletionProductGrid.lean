import Waring.EndgameCompletionProductCompleteSums
import Waring.ProductBoxGrid
import Waring.ProductBoxApprox

/-! # Exact finite product-grid to residue-ring transport -/

noncomputable section
open scoped BigOperators
namespace Waring.EndgameCompletion
open ProductBox QuadraticModulation

theorem sum_Icc_zmod (q : ℕ) [NeZero q] (F : ZMod q→ℂ) :
    (∑ n∈Finset.Icc 1 q,F (n : ZMod q))=∑ x : ZMod q,F x := by
  classical
  apply Finset.sum_bij (fun n _=>((n-1 : ℕ) : ZMod q)+1)
  · intro _ _
    exact Finset.mem_univ _
  · intro n hn m hm he
    have hn' := Finset.mem_Icc.mp hn
    have hm' := Finset.mem_Icc.mp hm
    have hv := congrArg ZMod.val (add_right_cancel he)
    rw [ZMod.val_natCast_of_lt (by omega : n-1<q),
      ZMod.val_natCast_of_lt (by omega : m-1<q)] at hv
    omega
  · intro x _
    refine ⟨(x-1).val+1,Finset.mem_Icc.mpr ⟨by omega,?_⟩,?_⟩
    · have hh := ZMod.val_lt (x-1)
      omega
    · simp only [Nat.add_sub_cancel_right,ZMod.natCast_zmod_val,sub_add_cancel]
  · intro n hn
    have hn1 := (Finset.mem_Icc.mp hn).1
    have he : ((n-1 : ℕ) : ZMod q)+1=(n : ZMod q) := by
      simpa only [Nat.cast_add,Nat.cast_one] using
        congrArg (fun m : ℕ=>(m : ZMod q)) (Nat.sub_add_cancel hn1)
    rw [he]

theorem gridSum_zmod (L q : ℕ) [NeZero q] (F : (Fin L→ZMod q)→ℂ) :
    gridSum L q (fun x=>F (fun i=>(x i : ZMod q)))=
      ∑ x : Fin L→ZMod q,F x := by
  classical
  induction L with
  | zero =>
      simp only [gridSum,Fintype.sum_unique]
      exact congrArg F (Subsingleton.elim _ _)
  | succ L ih =>
      have hcast (n : ℕ) (y : Fin L→ℕ) :
          (fun i : Fin (L+1)=>((Fin.cons (α := fun _ : Fin (L+1)=>ℕ) n y i : ℕ) : ZMod q))=
            Fin.cons (n : ZMod q) (fun i=>(y i : ZMod q)) := by
        funext i
        refine Fin.cases ?_ (fun j=>?_) i <;> rfl
      simp only [gridSum,hcast]
      have hinner (n : ℕ) :
          gridSum L q (fun y=>F (Fin.cons (n : ZMod q) (fun i=>(y i : ZMod q))))=
            ∑ y : Fin L→ZMod q,F (Fin.cons (n : ZMod q) y) :=
        ih (fun y=>F (Fin.cons (n : ZMod q) y))
      simp_rw [hinner]
      rw [sum_Icc_zmod q (fun z=>∑ y : Fin L→ZMod q,F (Fin.cons z y))]
      rw [← (Fin.consEquiv (fun _ : Fin (L+1)=>ZMod q)).sum_comp,Fintype.sum_prod_type]
      rfl

theorem gridMean_zmod (L q : ℕ) [NeZero q] (F : (Fin L→ZMod q)→ℂ) :
    gridMean L q (fun x=>F (fun i=>(x i : ZMod q)))=
      (∑ x : Fin L→ZMod q,F x)/(q : ℂ)^L := by
  rw [gridMean,gridSum_zmod]

theorem rational_product_gridMean_eq (k L q : ℕ) [NeZero q] (a : ℤ) :
    gridMean L q (fun x=>e ((a : ℝ)/q*(∏ i,(x i : ℝ))^k))=
      productCompleteSum q k L (a : ZMod q)/(q : ℂ)^L := by
  have hphase (x : Fin L→ℕ) :
      e ((a : ℝ)/q*(∏ i,(x i : ℝ))^k)=
        ZMod.stdAddChar ((a : ZMod q)*(∏ i,(x i : ZMod q))^k) := by
    have hh := stdAddChar_monomial_nat q k a (∏ i,x i)
    simpa only [Nat.cast_prod] using hh.symm
  simp_rw [hphase]
  exact gridMean_zmod L q (fun x=>ZMod.stdAddChar ((a : ZMod q)*(∏ i,x i)^k))

theorem rationalProductMean_eq_complete (k L q : ℕ) [NeZero q] (a : ℤ) :
    rationalProductMean k L a q=productCompleteSum q k L (a : ZMod q)/(q : ℂ)^L :=
  rational_product_gridMean_eq k L q a

#print axioms gridSum_zmod
#print axioms rational_product_gridMean_eq
#print axioms rationalProductMean_eq_complete
end Waring.EndgameCompletion
