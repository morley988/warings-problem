import WaringEnvelope.SemanticMenu
import WaringEnvelope.TerminalCosts

/-! # Extracting all applicable moment stages from a certified conductor menu -/
noncomputable section
namespace WaringEnvelope
open scoped BigOperators

structure IndexedStages (C : ℕ → ℝ → ℝ → ℝ → Prop) (k z₀ z m : ℕ) (R : ℝ) where
  N : ℕ
  height : ℕ → ℕ
  modulus : ℕ → ℕ
  first : height 0=z₀
  lastHeight : height N=z
  lastModulus : modulus N=m
  posHeight : ∀ i≤N, 0<height i
  posModulus : ∀ i≤N, B≤modulus i
  stage : ∀ i≤N, ConductorsAt C k (height i) (modulus i)
  decreasing : ∀ i<N, height (i+1)<height i
  increasing : ∀ i<N, modulus i≤modulus (i+1)
  gain : U*modulus 0*T>2*(T-z₀)*V*B
  cost : (∑ i∈Finset.range N, 2*Real.log ((height i:ℝ)/height (i+1))/length (modulus i))=R

theorem MathematicalMenu.indexed {C k z₀ z m R} (h : MathematicalMenu C k z₀ z m R)
    (h₀ : 0<z₀) : Nonempty (IndexedStages C k z₀ z m R) := by
  induction h with
  | initial m hm hs hg =>
    exact ⟨⟨0,fun _ => z₀,fun _ => m,rfl,rfl,rfl,fun _ _ => h₀,fun _ _ => hm,
      fun _ _ => hs,by omega,by omega,hg,by simp⟩⟩
  | @next z m R _ zz mm hz hzz hm hs ih =>
    obtain ⟨p⟩ := ih
    let H (i : ℕ) := if i≤p.N then p.height i else zz
    let M (i : ℕ) := if i≤p.N then p.modulus i else mm
    have hH (i : ℕ) (hi : i≤p.N) : H i=p.height i := if_pos hi
    have hM (i : ℕ) (hi : i≤p.N) : M i=p.modulus i := if_pos hi
    have hHz : H (p.N+1)=zz := if_neg (by omega)
    have hMm : M (p.N+1)=mm := if_neg (by omega)
    refine ⟨⟨p.N+1,H,M,(hH 0 (by omega)).trans p.first,hHz,hMm,?_,?_,?_,?_,?_,?_,?_⟩⟩
    · intro i hi
      rcases Nat.le_or_eq_of_le_succ hi with h|rfl
      · rw [hH i h];exact p.posHeight i h
      · rwa [hHz]
    · intro i hi
      rcases Nat.le_or_eq_of_le_succ hi with h|rfl
      · rw [hM i h];exact p.posModulus i h
      · rw [hMm]
        exact ((p.lastModulus ▸ p.posModulus p.N le_rfl) : B≤m) |>.trans hm
    · intro i hi
      rcases Nat.le_or_eq_of_le_succ hi with h|rfl
      · rw [hH i h,hM i h];exact p.stage i h
      · rwa [hHz,hMm]
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h|rfl
      · rw [hH _ (by omega),hH _ (by omega)];exact p.decreasing i h
      · rw [hHz,hH _ le_rfl,p.lastHeight];exact hzz
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h|rfl
      · rw [hM _ (by omega),hM _ (by omega)];exact p.increasing i h
      · rw [hMm,hM _ le_rfl,p.lastModulus];exact hm
    · rw [hM 0 (by omega)];exact p.gain
    · rw [Finset.sum_range_succ,hHz,hH _ le_rfl,hM _ le_rfl,p.lastHeight,p.lastModulus]
      have hrow : (∑ i∈Finset.range p.N, 2*Real.log ((H i:ℝ)/H (i+1))/length (M i))=R := by
        refine Eq.trans ?_ p.cost
        apply Finset.sum_congr rfl
        intro i hi
        have hl := Finset.mem_range.mp hi
        rw [hH i (by omega),hH (i+1) (by omega),hM i (by omega)]
      rw [hrow];rfl

#print axioms MathematicalMenu.indexed
end WaringEnvelope
