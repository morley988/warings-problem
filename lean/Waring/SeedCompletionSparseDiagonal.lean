import Waring.SeedCompletionSparseDiagonalCount

/-!
# The actual sparse simultaneous diagonal count

The first-coordinate swap turns the ordinary equal-sum system into the
signed system without changing the finite domain. This gives the required
J+1-variable bound for the exact progression p,2p,...,Jp.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseDiagonal

def progressionSolutions (p J s : ℕ) (A : Finset ℕ) :
    Finset ((Fin s → ℕ) × (Fin s → ℕ)) :=
  ((finiteTuples A s) ×ˢ (finiteTuples A s)).filter
    (fun xy => ∀r : Fin J,(∑i,(xy.1 i)^(p*(r.val+1)))=∑i,(xy.2 i)^(p*(r.val+1)))

def swapCenters {J : ℕ} (xy : (Fin (J+1) → ℕ) × (Fin (J+1) → ℕ)) :
    (Fin (J+1) → ℕ) × (Fin (J+1) → ℕ) :=
  (Fin.cons (xy.2 0) (fun i : Fin J => xy.1 i.succ),
    Fin.cons (xy.1 0) (fun i : Fin J => xy.2 i.succ))

theorem swapCenters_involutive (J : ℕ) : Function.Involutive (@swapCenters J) := by
  intro xy
  apply Prod.ext
  · ext i
    refine Fin.cases rfl (fun j => rfl) i
  · ext i
    refine Fin.cases rfl (fun j => rfl) i

theorem progression_card_le_signed (p J : ℕ) (A : Finset ℕ) :
    (progressionSolutions p J (J+1) A).card ≤ (signedSolutions p J A).card := by
  classical
  apply Finset.card_le_card_of_injOn swapCenters _ (swapCenters_involutive J).injective.injOn
  intro xy hxy
  obtain ⟨hxy,hs⟩ := Finset.mem_filter.mp hxy
  obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro i
      refine Fin.cases (Fintype.mem_piFinset.mp hy 0)
        (fun j => Fintype.mem_piFinset.mp hx j.succ) i
    · apply Fintype.mem_piFinset.mpr
      intro i
      refine Fin.cases (Fintype.mem_piFinset.mp hx 0)
        (fun j => Fintype.mem_piFinset.mp hy j.succ) i
  · intro r hr hrJ
    have hn := hs ⟨r-1,by omega⟩
    simp only [Nat.sub_add_cancel hr] at hn
    have hZ : (∑i,(xy.1 i : ℤ)^(p*r))=∑i,(xy.2 i : ℤ)^(p*r) := by exact_mod_cast hn
    simp only [Fin.sum_univ_succ] at hZ
    simp only [sparseSignedMoment,swapCenters,Fin.cons_zero,Fin.cons_succ]
    linear_combination hZ

theorem progression_solutions_subpower (p J : ℕ) (hp : 0 < p) (hJ : 2 ≤ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∃C : ℝ,0 < C ∧ ∀N : ℕ,1 ≤ N →
      ((progressionSolutions p J (J+1) (Finset.Icc 1 N)).card : ℝ) ≤
        C*(N : ℝ)^((J+1 : ℕ)+ε) := by
  obtain ⟨C,hC,hbound⟩ := signed_solutions_subpower p J hp hJ hε
  refine ⟨C,hC,?_⟩
  intro N hN
  have hb := hbound N (by exact_mod_cast hN) (Finset.Icc 1 N)
    (fun n hn => by exact_mod_cast (Finset.mem_Icc.mp hn).2)
    (by simp)
  exact (show ((progressionSolutions p J (J+1) (Finset.Icc 1 N)).card : ℝ) ≤
    ((signedSolutions p J (Finset.Icc 1 N)).card : ℝ) by
      exact_mod_cast progression_card_le_signed p J (Finset.Icc 1 N)).trans hb

theorem even_progression_solutions_subpower (k J : ℕ) (hk : 1 ≤ k) (hJ : 2 ≤ J)
    {ε : ℝ} (hε : 0 < ε) :
    ∃C : ℝ,0 < C ∧ ∀N : ℕ,1 ≤ N →
      ((progressionSolutions (2*k) J (J+1) (Finset.Icc 1 N)).card : ℝ) ≤
        C*(N : ℝ)^((J+1 : ℕ)+ε) :=
  progression_solutions_subpower (2*k) J (by omega) hJ hε

#print axioms progression_solutions_subpower
#print axioms even_progression_solutions_subpower
end Waring.SeedCompletionSparseDiagonal
