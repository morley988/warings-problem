import Waring.AuxiliaryCounting
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Vector coefficient collisions and the proved list count

The L2 argument uses coordinate-indexed h,m,n vectors. The divisor induction
uses a reversed list of blocks. This file proves the literal finite-count
translation; neither count is replaced by a recurrence proxy.
-/

noncomputable section
open scoped BigOperators
namespace Waring.AuxiliaryTupleCount
open Waring.AuxiliaryCounting Waring.PowerDifferenceFibers

def tupleFamily (H M : ℕ → ℕ) (r : ℕ) : Finset (Fin r → Block) :=
  Fintype.piFinset (fun i : Fin r => blockRange (H i.val) (M i.val))

def tupleList {r : ℕ} (x : Fin r → Block) : List Block := (List.ofFn x).reverse

theorem tupleList_injective (r : ℕ) : Function.Injective (@tupleList r) := by
  intro x y h
  apply List.ofFn_injective
  exact List.reverse_injective h

theorem tupleList_succ {r : ℕ} (x : Fin (r+1) → Block) :
    tupleList x = x (Fin.last r)::tupleList (fun i : Fin r => x i.castSucc) := by
  simp only [tupleList,List.ofFn_succ',List.concat_eq_append,List.reverse_append,
    List.reverse_singleton,List.singleton_append]

theorem tupleList_mem_prefix (H M : ℕ → ℕ) (r : ℕ) (x : Fin r → Block)
    (hx : x ∈ tupleFamily H M r) : tupleList x ∈ prefixFamily H M r := by
  induction r with
  | zero => simp [tupleList,prefixFamily]
  | succ r ih =>
      have hprev : (fun i : Fin r => x i.castSucc) ∈ tupleFamily H M r := by
        apply Fintype.mem_piFinset.mpr
        intro i
        exact Fintype.mem_piFinset.mp hx i.castSucc
      have hlast : x (Fin.last r) ∈ blockRange (H r) (M r) :=
        Fintype.mem_piFinset.mp hx (Fin.last r)
      change tupleList x ∈ (prefixFamily H M r ×ˢ blockRange (H r) (M r)).image
        (fun p : List Block × Block => p.2::p.1)
      refine Finset.mem_image.mpr ⟨(tupleList (fun i : Fin r => x i.castSucc),x (Fin.last r)),
        Finset.mem_product.mpr ⟨ih _ hprev,hlast⟩,?_⟩
      exact (tupleList_succ x).symm

theorem sumValue_tupleList (k r : ℕ) (x : Fin r → Block) :
    sumValue k (tupleList x) = ∑ i, blockValue k (x i) := by
  simp [sumValue,tupleList,List.map_reverse,List.map_ofFn,List.sum_ofFn]

theorem tuple_zeroCount_le (k r : ℕ) (H M : ℕ → ℕ) :
    ((tupleFamily H M r).filter (fun x => ∑ i, blockValue k (x i)=0)).card ≤
      zeroCount k (prefixFamily H M r) := by
  apply Finset.card_le_card_of_injOn tupleList
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hmem,hzero⟩
    exact Finset.mem_filter.mpr ⟨tupleList_mem_prefix H M r x hmem,
      (sumValue_tupleList k r x).trans hzero⟩
  · intro x hx y hy hxy
    exact tupleList_injective r hxy

def coordinateBox (B : ℕ → ℕ) (r : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun i : Fin r => Finset.Icc 1 (B i.val))

def blocksOfVectors {r : ℕ}
    (x : (Fin r → ℕ) × ((Fin r → ℕ) × (Fin r → ℕ))) : Fin r → Block :=
  fun i => ⟨x.1 i,x.2.1 i,x.2.2 i⟩

theorem blocksOfVectors_injective (r : ℕ) : Function.Injective (@blocksOfVectors r) := by
  intro x y h
  apply Prod.ext
  · funext i
    exact congrArg Block.h (congrFun h i)
  · apply Prod.ext
    · funext i
      exact congrArg Block.m (congrFun h i)
    · funext i
      exact congrArg Block.n (congrFun h i)

theorem vector_collision_count_le (k r : ℕ) (H M : ℕ → ℕ) :
    (∑ h ∈ coordinateBox H r,
      (((coordinateBox M r) ×ˢ (coordinateBox M r)).filter (fun mn =>
        ∑ i : Fin r, (h i:ℤ)^2*((mn.1 i:ℤ)^k-(mn.2 i:ℤ)^k)=0)).card) ≤
      zeroCount k (prefixFamily H M r) := by
  classical
  let S := ((coordinateBox H r) ×ˢ ((coordinateBox M r) ×ˢ (coordinateBox M r))).filter
    (fun x => ∑ i : Fin r, (x.1 i:ℤ)^2*((x.2.1 i:ℤ)^k-(x.2.2 i:ℤ)^k)=0)
  have heq : (∑ h ∈ coordinateBox H r,
      (((coordinateBox M r) ×ˢ (coordinateBox M r)).filter (fun mn =>
        ∑ i : Fin r, (h i:ℤ)^2*((mn.1 i:ℤ)^k-(mn.2 i:ℤ)^k)=0)).card) = S.card := by
    simp only [S,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product]
  rw [heq]
  apply le_trans _ (tuple_zeroCount_le k r H M)
  apply Finset.card_le_card_of_injOn blocksOfVectors
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hmem,hzero⟩
    rcases Finset.mem_product.mp hmem with ⟨hh,hmn⟩
    rcases Finset.mem_product.mp hmn with ⟨hm,hn⟩
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro i
      exact mem_blockRange.mpr ⟨Fintype.mem_piFinset.mp hh i,
        Fintype.mem_piFinset.mp hm i,Fintype.mem_piFinset.mp hn i⟩
    · simpa only [blocksOfVectors,blockValue] using hzero
  · intro x hx y hy hxy
    exact blocksOfVectors_injective r hxy

#print axioms vector_collision_count_le

end Waring.AuxiliaryTupleCount
