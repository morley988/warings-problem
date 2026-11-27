import Waring.AuxiliaryL2Grouping

/-! # Divisor grouping on literal Cartesian parameter domains -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionProductGrouping
open AuxiliaryL2Grouping

theorem classFiber_product {ι κ ν : Type*} [DecidableEq ν]
    (H : Finset ι) (B : Finset κ) (key : ι → ν)
    (hinj : Set.InjOn key (↑H : Set ι)) {h : ι} (hh : h ∈ H) :
    classFiber (H ×ˢ B) (fun p => key p.1) (key h) = {h} ×ˢ B := by
  classical
  ext p
  constructor
  · intro hp
    have hm := Finset.mem_filter.mp hp
    have hh' := (Finset.mem_product.mp hm.1).1
    have heq := hinj hh' hh hm.2
    exact Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr heq,
      (Finset.mem_product.mp hm.1).2⟩
  · intro hp
    have hm := Finset.mem_product.mp hp
    have heq := Finset.mem_singleton.mp hm.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heq ▸ hh,hm.2⟩,
      congrArg key heq⟩

theorem collision_singleton_product_card {ι κ : Type*}
    (h : ι) (B : Finset κ) (f : ι → κ → ℤ) :
    (collisionPairs ({h} ×ˢ B) (fun p => f p.1 p.2)).card =
      (collisionPairs B (f h)).card := by
  classical
  simp only [collisionPairs,Finset.card_eq_sum_ones,Finset.sum_filter,Finset.sum_product,
    Finset.sum_singleton]


theorem sum_product_classes {ι κ ν : Type*} [DecidableEq ν]
    (H : Finset ι) (B : Finset κ) (f : ι → κ → ℤ) (key : ι → ν)
    (hinj : Set.InjOn key (↑H : Set ι)) :
    (∑ l ∈ H.image key,
      ((collisionPairs (classFiber (H ×ˢ B) (fun p => key p.1) l)
        (fun p => f p.1 p.2)).card : ℝ)) =
      ∑ h ∈ H, ((collisionPairs B (f h)).card : ℝ) := by
  classical
  rw [Finset.sum_image (fun h hh h' hh' he => hinj hh hh' he)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [classFiber_product H B key hinj hh,collision_singleton_product_card]

/-- A subpower loss groups only the actual divisor labels at each frequency.
The right side retains the exact within-parameter collision counts. -/
theorem second_moment_divisor_product (r : ℕ) {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P →
      ∀ (ι κ : Type*) (H : Finset ι) (B : Finset κ)
        (f : ι → κ → ℤ) (key : ι → Fin r → ℕ),
      Set.InjOn key (↑H : Set ι) →
      (∀ h ∈ H,∀ x ∈ B,f h x ≠ 0 ∧ ((f h x).natAbs : ℝ) ≤ P^L) →
      (∀ h ∈ H,∀ x ∈ B,∀ i,(key h i : ℤ) ∣ f h x) →
      (∫ α in (0 : ℝ)..1,
        ‖∑ p ∈ H ×ˢ B,fourier (f p.1 p.2) (α : AddCircle (1 : ℝ))‖^2) ≤
        C*P^ε*∑ h ∈ H, ((collisionPairs B (f h)).card : ℝ) := by
  obtain ⟨C,hC,hbound⟩ := frequency_key_multiplicity r hL hε
  refine ⟨C,hC,?_⟩
  intro P hP ι κ H B f key hinj hsize hdvd
  classical
  have hmap : ∀ p ∈ H ×ˢ B,key p.1 ∈ H.image key :=
    fun p hp => Finset.mem_image_of_mem key (Finset.mem_product.mp hp).1
  have hm := hbound P hP (ι×κ) (H ×ˢ B) (fun p => f p.1 p.2) (fun p => key p.1)
    (fun p hp => hsize p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
    (fun p hp i => hdvd p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2 i)
  have hb := secondMoment_le_classes (H ×ˢ B) (fun p => f p.1 p.2)
    (fun p => key p.1) (H.image key) hmap (by positivity : 0 ≤ C*P^ε) hm
  rwa [sum_product_classes H B f key hinj] at hb

#print axioms second_moment_divisor_product
end Waring.SeedCompletionProductGrouping
