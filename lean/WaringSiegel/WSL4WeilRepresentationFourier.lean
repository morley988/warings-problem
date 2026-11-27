import WaringSiegel.WSL3MomentRepresentationFourier

/-! # A nonzero four-by-four Fourier coefficient gives eight actual roots

The two finite node families may differ. Zero extension to their disjoint
union makes the existing exact product orthogonality theorem applicable.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace WaringSiegel.WSL4Weil
open MeasureTheory NumberField WSL3
open scoped NumberField BigOperators Classical
variable {K : Type*} [Field K] [NumberField K]

theorem traceWeylSum_sum_left
    {A B : Type*} [Fintype A] [Fintype B] (k : ℕ)
    (a : A → 𝓞 K) (b : B → 𝓞 K) (w : A → ℂ) (q : ArchimedeanTraceTorus K) :
    traceWeylSum k (Sum.elim a b) (Sum.elim w (fun _ => 0)) q =
      traceWeylSum k a w q := by
  simp [traceWeylSum,Fintype.sum_sum_type]

theorem traceWeylSum_sum_right
    {A B : Type*} [Fintype A] [Fintype B] (k : ℕ)
    (a : A → 𝓞 K) (b : B → 𝓞 K) (w : B → ℂ) (q : ArchimedeanTraceTorus K) :
    traceWeylSum k (Sum.elim a b) (Sum.elim (fun _ => 0) w) q =
      traceWeylSum k b w q := by
  simp [traceWeylSum,Fintype.sum_sum_type]

theorem four_by_four_fourier_ne_zero_has_solution
    {A B : Type*} [Fintype A] [Fintype B] (k : ℕ)
    (a : A → 𝓞 K) (b : B → 𝓞 K) (w : A → ℂ) (v : B → ℂ) (target : 𝓞 K)
    (hne : (∫ q, (traceWeylSum k a w q)^4*(traceWeylSum k b v q)^4*
      traceTorusCharacter (-target) q ∂traceHaar) ≠ 0) :
    ∃ x : Fin 8 → 𝓞 K,
      (∀ i, (∃ u : A, x i = a u) ∨ (∃ u : B, x i = b u)) ∧
      ∑ i, (x i)^k = target := by
  let J := Fin 4 ⊕ Fin 4
  let nodes : J → A ⊕ B → 𝓞 K := fun _ => Sum.elim a b
  let weights : J → A ⊕ B → ℂ :=
    Sum.elim (fun _ => Sum.elim w (fun _ => 0))
      (fun _ => Sum.elim (fun _ => 0) v)
  have hprod (q : ArchimedeanTraceTorus K) :
      (∏ i : J, traceWeylSum k (nodes i) (weights i) q) =
        (traceWeylSum k a w q)^4*(traceWeylSum k b v q)^4 := by
    rw [Fintype.prod_sum_type]
    simp only [nodes,weights,Sum.elim_inl,Sum.elim_inr,traceWeylSum_sum_left,
      traceWeylSum_sum_right,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hne' : (∫ q, (∏ i : J, traceWeylSum k (nodes i) (weights i) q)*
      traceTorusCharacter (-target) q ∂traceHaar) ≠ 0 := by
    simpa only [hprod] using hne
  have hex : ∃ z : J → A ⊕ B, (∑ i, (nodes i (z i))^k)=target := by
    by_contra hn
    apply hne'
    rw [traceWeylSum_product_fourier_coefficient]
    apply Finset.sum_eq_zero
    intro z _
    exact if_neg (fun hz => hn ⟨z,hz⟩)
  obtain ⟨z,hz⟩ := hex
  let e : Fin 8 ≃ J := (finSumFinEquiv : Fin 4 ⊕ Fin 4 ≃ Fin (4+4)).symm
  let x : Fin 8 → 𝓞 K := fun i => nodes (e i) (z (e i))
  refine ⟨x,?_,?_⟩
  · intro i
    cases hi : z (e i) with
    | inl u => exact Or.inl ⟨u,by simp only [x,nodes,hi,Sum.elim_inl]⟩
    | inr u => exact Or.inr ⟨u,by simp only [x,nodes,hi,Sum.elim_inr]⟩
  · have he := e.bijective.sum_comp (fun i : J => (nodes i (z i))^k)
    exact he.trans hz
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.four_by_four_fourier_ne_zero_has_solution
