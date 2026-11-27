import Waring.SeedCompletionSparseDiagonalFibers

/-! # The zero-product branch of the sparse diagonal count

The product vanishes exactly when a head coordinate equals the distinguished
coordinate. This leaves at most J|A|^J possible right tuples. For each such
tuple and each distinguished left coordinate, Newton's identities leave at
most J^J left tuples. Every finite counting map is explicit.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseDiagonal

def degenerateTuples (p J : ℕ) (A : Finset ℕ) : Finset (Fin (J+1) → ℕ) :=
  (finiteTuples A (J+1)).filter (fun y => differenceProduct p y=0)

theorem degenerate_card_le {p J : ℕ} (hp : 0 < p) (A : Finset ℕ) :
    (degenerateTuples p J A).card ≤ J*A.card^J := by
  classical
  let imageAt (i : Fin J) := (finiteTuples A J).image
    (fun z : Fin J → ℕ => Fin.cons (α := fun _ => ℕ) (z i) z)
  have hsub : degenerateTuples p J A ⊆ Finset.univ.biUnion imageAt := by
    intro y hy
    obtain ⟨hyA,hzero⟩ := Finset.mem_filter.mp hy
    have hz := Finset.prod_eq_zero_iff.mp hzero
    obtain ⟨i,hi,hzi⟩ := hz
    have he : y 0=y i.succ := Nat.pow_left_injective hp.ne' (by
      have he' := sub_eq_zero.mp hzi
      exact_mod_cast he')
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(fun l : Fin J => y l.succ),?_,?_⟩
    · apply Fintype.mem_piFinset.mpr
      intro l
      exact Fintype.mem_piFinset.mp hyA l.succ
    · ext l
      refine Fin.cases he.symm (fun j => rfl) l
  calc
    _ ≤ (Finset.univ.biUnion imageAt).card := Finset.card_le_card hsub
    _ ≤ ∑i : Fin J,(imageAt i).card := Finset.card_biUnion_le
    _ ≤ ∑_i : Fin J,A.card^J := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.card_image_le).trans_eq (by simp [finiteTuples,Fintype.card_piFinset])
    _ = _ := by simp

theorem fixed_center_signed_family_card_le {p J : ℕ} (hp : 0 < p)
    (S : Finset (Fin (J+1) → ℕ)) (c : ℕ) (hc : ∀x∈S,x 0=c)
    (hs : ∀x∈S,∀y∈S,∀ r : ℕ, 1 ≤ r → r ≤ J →
      sparseSignedMoment p x r=sparseSignedMoment p y r) : S.card ≤ J^J := by
  classical
  let head : (Fin (J+1) → ℕ) → (Fin J → ℕ) := fun x i => x i.succ
  have hi : Set.InjOn head S := by
    intro x hx y hy he
    ext i
    refine Fin.cases ((hc x hx).trans (hc y hy).symm) (fun j => congrFun he j) i
  rw [← Finset.card_image_of_injOn hi]
  apply power_family_card_le hp
  intro x hx y hy r hr hrJ
  obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
  have he := hs x' hx' y' hy' r hr hrJ
  unfold sparseSignedMoment at he
  rw [hc x' hx',hc y' hy'] at he
  exact sub_left_injective he

def signedSolutions (p J : ℕ) (A : Finset ℕ) :
    Finset ((Fin (J+1) → ℕ) × (Fin (J+1) → ℕ)) :=
  ((finiteTuples A (J+1)) ×ˢ (finiteTuples A (J+1))).filter
    (fun xy => ∀ r : ℕ, 1 ≤ r → r ≤ J →
      sparseSignedMoment p xy.1 r=sparseSignedMoment p xy.2 r)

def zeroSignedSolutions (p J : ℕ) (A : Finset ℕ) :
    Finset ((Fin (J+1) → ℕ) × (Fin (J+1) → ℕ)) :=
  (signedSolutions p J A).filter (fun xy => differenceProduct p xy.2=0)

theorem zero_signed_solutions_card_le {p J : ℕ} (hp : 0 < p) (A : Finset ℕ) :
    (zeroSignedSolutions p J A).card ≤ (J*J^J)*A.card^(J+1) := by
  classical
  let E := zeroSignedSolutions p J A
  let key : ((Fin (J+1) → ℕ) × (Fin (J+1) → ℕ)) → ((Fin (J+1) → ℕ) × ℕ) :=
    fun xy => (xy.2,xy.1 0)
  have hmap : Set.MapsTo key E
      (↑(degenerateTuples p J A ×ˢ A) : Set ((Fin (J+1) → ℕ) × ℕ)) := by
    intro xy hxy
    obtain ⟨hsol,hzero⟩ := Finset.mem_filter.mp hxy
    obtain ⟨hbox,hs⟩ := Finset.mem_filter.mp hsol
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hbox
    change (xy.2,xy.1 0) ∈ degenerateTuples p J A ×ˢ A
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hy,hzero⟩,
      Fintype.mem_piFinset.mp hx 0⟩
  have hfiber (q : (Fin (J+1) → ℕ) × ℕ) :
      (E.filter (fun xy => key xy=q)).card ≤ J^J := by
    let F := E.filter (fun xy => key xy=q)
    have hi : Set.InjOn (fun xy : (Fin (J+1) → ℕ) × (Fin (J+1) → ℕ) => xy.1) F := by
      intro x hx y hy he
      apply Prod.ext he
      exact (congrArg Prod.fst (Finset.mem_filter.mp hx).2).trans
        (congrArg Prod.fst (Finset.mem_filter.mp hy).2).symm
    rw [← Finset.card_image_of_injOn hi]
    apply fixed_center_signed_family_card_le hp _ q.2
    · intro x hx
      obtain ⟨xy,hxy,rfl⟩ := Finset.mem_image.mp hx
      exact congrArg Prod.snd (Finset.mem_filter.mp hxy).2
    · intro x hx y hy r hr hrJ
      obtain ⟨xy,hxy,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨yz,hyz,rfl⟩ := Finset.mem_image.mp hy
      have hsx := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hxy).1).1).2 r hr hrJ
      have hsy := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hyz).1).1).2 r hr hrJ
      have hxyq := congrArg Prod.fst (Finset.mem_filter.mp hxy).2
      have hyzq := congrArg Prod.fst (Finset.mem_filter.mp hyz).2
      change xy.2=q.1 at hxyq
      change yz.2=q.1 at hyzq
      rw [hxyq] at hsx
      rw [hyzq] at hsy
      exact hsx.trans hsy.symm
  change E.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑_q∈degenerateTuples p J A ×ˢ A,J^J := Finset.sum_le_sum (fun q _ => hfiber q)
    _ = ((degenerateTuples p J A).card*A.card)*J^J := by simp
    _ ≤ ((J*A.card^J)*A.card)*J^J := by gcongr; exact degenerate_card_le hp A
    _ = _ := by rw [pow_succ]; ring

#print axioms degenerate_card_le
#print axioms zero_signed_solutions_card_le
end Waring.SeedCompletionSparseDiagonal
