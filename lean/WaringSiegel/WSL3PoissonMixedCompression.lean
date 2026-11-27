import WaringSiegel.WSL2MomentCubicCompressionGrowth

/-! # Asymmetric divisor compression, preserving the small shift count -/
set_option maxHeartbeats 100000
noncomputable section
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL3Poisson
open WSL2
variable {R : Type*} [CommRing R] [IsDomain R]

def rectangleProducts (U V : Finset R) : Finset R :=
  (U.product V).image (fun p => p.1*p.2)

theorem rectangleProducts_subset (U V : Finset R) :
    rectangleProducts U V ⊆ shiftProducts (U ∪ V) := by
  intro a ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_image.mpr ⟨p,Finset.mem_product.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_product.mp hp).1,
      Finset.mem_union_right _ (Finset.mem_product.mp hp).2⟩,rfl⟩

theorem rectangle_zero_fiber_card_le (U V : Finset R) (hU : ∀ h ∈ U, h ≠ 0) :
    ((U.product V).filter (fun p => p.1*p.2=0)).card ≤ U.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq he
    have hpU := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hqU := (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    have hp0 : p.2 = 0 := (mul_eq_zero.mp (Finset.mem_filter.mp hp).2).resolve_left (hU p.1 hpU)
    have hq0 : q.2 = 0 := (mul_eq_zero.mp (Finset.mem_filter.mp hq).2).resolve_left (hU q.1 hqU)
    exact Prod.ext he (hp0.trans hq0.symm)

theorem rectangle_product_kernel_sum_eq (U V : Finset R) (F : R → ℝ) :
    (∑ h ∈ U, ∑ j ∈ V, F (h*j)) =
      ∑ a ∈ rectangleProducts U V,
        (((U.product V).filter (fun p => p.1*p.2=a)).card:ℝ)*F a := by
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s:=U.product V) (t:=rectangleProducts U V) (g:=fun p => p.1*p.2)
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩) (fun p => F (p.1*p.2))
  calc
    _ = ∑ p ∈ U.product V, F (p.1*p.2) := (Finset.sum_product U V _).symm
    _ = ∑ a ∈ rectangleProducts U V, ∑ p ∈ (U.product V).filter (fun p => p.1*p.2=a), F (p.1*p.2) :=
      hfiber.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        _ = ∑ _p ∈ (U.product V).filter (fun p => p.1*p.2=a), F a := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
        _ = _ := by simp

theorem rectangle_product_kernel_sum_le (U V : Finset R) (hU : ∀ h ∈ U, h ≠ 0)
    (F : R → ℝ) (hF : ∀ a, 0 ≤ F a) (D : ℝ)
    (hD : ∀ a ∈ rectangleProducts U V, a ≠ 0 →
      (((U.product V).filter (fun p => p.1*p.2=a)).card:ℝ) ≤ D) :
    (∑ h ∈ U, ∑ j ∈ V, F (h*j)) ≤
      (U.card:ℝ)*F 0 + D*∑ a ∈ (rectangleProducts U V).filter (fun a => a ≠ 0), F a := by
  rw [rectangle_product_kernel_sum_eq]
  have hpoint (a) (ha : a ∈ rectangleProducts U V) :
      (((U.product V).filter (fun p => p.1*p.2=a)).card:ℝ)*F a ≤
        (if a=0 then (U.card:ℝ)*F 0 else 0)+D*(if a≠0 then F a else 0) := by
    by_cases hz : a=0
    · subst a
      simp only [if_pos rfl,ne_eq,not_true_eq_false,if_false,mul_zero,add_zero]
      have hc : (((U.product V).filter (fun p => p.1*p.2=0)).card:ℝ) ≤ U.card := by
        exact_mod_cast rectangle_zero_fiber_card_le U V hU
      exact mul_le_mul_of_nonneg_right hc (hF 0)
    · simp only [if_neg hz,if_pos hz,zero_add]
      exact mul_le_mul_of_nonneg_right (hD a ha hz) (hF a)
  calc
    _ ≤ ∑ a ∈ rectangleProducts U V,
        ((if a=0 then (U.card:ℝ)*F 0 else 0)+D*(if a≠0 then F a else 0)) :=
      Finset.sum_le_sum hpoint
    _ = (if 0 ∈ rectangleProducts U V then (U.card:ℝ)*F 0 else 0)+
        D*∑ a ∈ (rectangleProducts U V).filter (fun a => a ≠ 0), F a := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_ite_eq',← Finset.sum_filter]
    _ ≤ _ := by
      apply add_le_add_right
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (Nat.cast_nonneg _) (hF 0)

variable {K : Type*} [Field K] [NumberField K]

theorem numberField_rectangle_kernel_rpow_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ U V : Finset (𝓞 K),
      (∀ h ∈ U, h ≠ 0) →
      (∀ h ∈ U, ∀ v : NumberField.InfinitePlace K, v (h:K) ≤ 2*P) →
      (∀ h ∈ V, ∀ v : NumberField.InfinitePlace K, v (h:K) ≤ 2*P) →
      ∀ F : 𝓞 K → ℝ, (∀ a, 0 ≤ F a) →
      (∑ h ∈ U, ∑ j ∈ V, F (h*j)) ≤ (U.card:ℝ)*F 0 +
        C*P^ε*∑ a ∈ (rectangleProducts U V).filter (fun a => a ≠ 0), F a := by
  obtain ⟨C,hC,hbound⟩ := shiftProductDivisors_rpow_bound (K:=K) hε
  refine ⟨C,hC,fun P hP U V hU0 hU hV F hF => ?_⟩
  apply rectangle_product_kernel_sum_le U V hU0 F hF (C*P^ε)
  intro a ha ha0
  have hbox : ∀ h ∈ U ∪ V, ∀ v : NumberField.InfinitePlace K, v (h:K) ≤ 2*P := by
    intro h hh v
    rcases Finset.mem_union.mp hh with hh | hh
    · exact hU h hh v
    · exact hV h hh v
  have hsub : ((U.product V).filter (fun p => p.1*p.2=a)).card ≤
      (((U ∪ V).product (U ∪ V)).filter (fun p => p.1*p.2=a)).card := by
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hm,he⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_product.mp hm).1,
        Finset.mem_union_right _ (Finset.mem_product.mp hm).2⟩,he⟩
  have hc : (((U.product V).filter (fun p => p.1*p.2=a)).card:ℝ) ≤
      (((U ∪ V).filter (fun h => h ≠ 0 ∧ h ∣ a)).card:ℝ) := by
    exact_mod_cast hsub.trans (product_fiber_card_le_divisors (U ∪ V) ha0)
  exact hc.trans (hbound P hP (U ∪ V) hbox a (rectangleProducts_subset U V ha) ha0)

end WaringSiegel.WSL3Poisson
