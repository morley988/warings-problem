import Waring.SeedCompletionSparseDiagonal

/-! # Uniform sparse progression estimates for all s ≤ J+1 -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSparseDiagonal

theorem progression_small_card_le {p J s : ℕ} (hp : 0 < p) (hsJ : s ≤ J)
    (A : Finset ℕ) :
    (progressionSolutions p J s A).card ≤ s^s * A.card^s := by
  classical
  let E := progressionSolutions p J s A
  have hmap : Set.MapsTo (fun xy : (Fin s → ℕ) × (Fin s → ℕ) => xy.2)
      E (finiteTuples A s) := by
    intro xy hxy
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hxy).1).2
  have hfiber (y : Fin s → ℕ) : (E.filter (fun xy => xy.2=y)).card ≤ s^s := by
    let F := E.filter (fun xy => xy.2=y)
    have hi : Set.InjOn (fun xy : (Fin s → ℕ) × (Fin s → ℕ) => xy.1) F := by
      intro x hx z hz he
      exact Prod.ext he ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hz).2.symm)
    change F.card ≤ _
    rw [← Finset.card_image_of_injOn hi]
    apply power_family_card_le hp
    intro x hx z hz r hr hrs
    obtain ⟨xy,hxy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨zy,hzy,rfl⟩ := Finset.mem_image.mp hz
    have hsx := (Finset.mem_filter.mp (Finset.mem_filter.mp hxy).1).2
      (⟨r-1,by omega⟩ : Fin J)
    have hsz := (Finset.mem_filter.mp (Finset.mem_filter.mp hzy).1).2
      (⟨r-1,by omega⟩ : Fin J)
    simp only [Nat.sub_add_cancel hr] at hsx hsz
    rw [(Finset.mem_filter.mp hxy).2] at hsx
    rw [(Finset.mem_filter.mp hzy).2] at hsz
    exact_mod_cast hsx.trans hsz.symm
  change E.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ _y ∈ finiteTuples A s, s^s := Finset.sum_le_sum (fun y _ => hfiber y)
    _ = _ := by simp [finiteTuples,Fintype.card_piFinset,Nat.mul_comm]

theorem progression_solutions_subpower_uniform (p J s : ℕ) (hp : 0 < p)
    (hJ : 2 ≤ J) (hs : 1 ≤ s) (hsJ : s ≤ J+1) {ε : ℝ} (hε : 0 < ε) :
    ∃C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M → ∀ A : Finset ℕ,
      (∀ a ∈ A, (a : ℝ) ≤ M) → (A.card : ℝ) ≤ M →
      ((progressionSolutions p J s A).card : ℝ) ≤ C * M^((s : ℝ)+ε) := by
  by_cases he : s=J+1
  · subst s
    obtain ⟨C,hC,hbound⟩ := signed_solutions_subpower p J hp hJ hε
    refine ⟨C,hC,?_⟩
    intro M hM A hA hcard
    apply le_trans _ (hbound M hM A hA hcard)
    exact_mod_cast progression_card_le_signed p J A
  · have hsJ' : s ≤ J := by omega
    refine ⟨(s : ℝ)^s,by positivity,?_⟩
    intro M hM A hA hcard
    have hMpos : 0 < M := zero_lt_one.trans_le hM
    have hb : ((progressionSolutions p J s A).card : ℝ) ≤
        (s : ℝ)^s * (A.card : ℝ)^s := by
      exact_mod_cast progression_small_card_le hp hsJ' A
    calc
      _ ≤ (s : ℝ)^s * M^s := hb.trans (by gcongr)
      _ ≤ (s : ℝ)^s * (M^s * M^ε) := by
        have hh := mul_le_mul_of_nonneg_left (Real.one_le_rpow hM hε.le)
          (show 0 ≤ (s : ℝ)^s * M^s by positivity)
        nlinarith only [hh]
      _ = _ := by rw [← Real.rpow_natCast M s, ← Real.rpow_add hMpos]

#print axioms progression_solutions_subpower_uniform
end Waring.SeedCompletionSparseDiagonal
