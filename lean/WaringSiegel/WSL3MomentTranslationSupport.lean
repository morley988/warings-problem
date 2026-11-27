import WaringSiegel.WSL3PoissonMixedSupport
import WaringSiegel.WSL3MomentPointwiseInsertionGrowth

/-! # Finite common-translation domains without an extra cardinality loss -/
noncomputable section
set_option maxHeartbeats 800000
open NumberField NumberField.mixedEmbedding
open scoped BigOperators Classical NumberField
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {G : Type*} [AddCommGroup G]

def translatedUnion (S Y : Finset G) : Finset G :=
  Y.biUnion (fun z => S.image (fun x => x-z))

theorem mem_translatedUnion (S Y : Finset G) {x z : G} (hx : x∈S) (hz : z∈Y) :
    x-z ∈ translatedUnion S Y :=
  Finset.mem_biUnion.mpr ⟨z, hz, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

theorem finite_sum_common_translate (w ψ : G → ℂ) (S T : Finset G) (z : G)
    (hsupp : ∀ x, w x ≠ 0 → x∈S) (hT : ∀ x∈S, x-z∈T) :
    (∑ x : S, w x.val*ψ x.val) = ∑ a : T, w (a.val+z)*ψ (a.val+z) := by
  rw [Finset.sum_coe_sort S (fun x => w x*ψ x),
    Finset.sum_coe_sort T (fun x => w (x+z)*ψ (x+z))]
  let U := S.image (fun x => x-z)
  have huT : U ⊆ T := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact hT x hx
  calc
    _ = ∑ a∈U, w (a+z)*ψ (a+z) := by
      rw [Finset.sum_image]
      · simp only [sub_add_cancel]
      · intro a ha b hb hab
        simpa only [sub_add_cancel] using congrArg (fun q : G => q+z) hab
    _ = _ := Finset.sum_subset huT (by
      intro a ha hnot
      have hz : w (a+z)=0 := by
        by_contra hn
        exact hnot (Finset.mem_image.mpr ⟨a+z, hsupp (a+z) hn, add_sub_cancel_right _ _⟩)
      rw [hz, zero_mul])

variable {K : Type*} [Field K] [NumberField K]

theorem translatedUnion_place_bound (S Y : Finset (𝓞 K)) (A P : ℝ)
    (hS : ∀ x∈S, ∀ v : InfinitePlace K, v (x:K) ≤ A*P)
    (hY : ∀ z∈Y, ∀ v : InfinitePlace K, v (z:K) ≤ P) :
    ∀ a∈translatedUnion S Y, ∀ v : InfinitePlace K, v (a:K) ≤ (A+1)*P := by
  intro a ha v
  obtain ⟨z,hz,ha⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
  change v ((x:K)-(z:K)) ≤ (A+1)*P
  calc
    v ((x:K)-(z:K)) ≤ v (x:K)+v (z:K) := v.val.sub_le_add _ _
    _ ≤ A*P+P := add_le_add (hS x hx v) (hY z hz v)
    _ = _ := by ring

theorem compact_support_place_bound (f : mixedSpace K → ℂ) (hc : HasCompactSupport f) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ P : ℝ, 0 < P → ∀ x : 𝓞 K,
      f (P⁻¹ • mixedEmbedding K (x:K)) ≠ 0 →
      ∀ v : InfinitePlace K, v (x:K) ≤ A*P := by
  obtain ⟨A, hA⟩ := isBounded_iff_forall_norm_le.mp hc.isBounded
  refine ⟨max 1 A, le_max_left _ _, ?_⟩
  intro P hP x hx v
  have hb : ‖P⁻¹ • mixedEmbedding K (x:K)‖ ≤ A := hA _ (subset_closure hx)
  have hp := (mixed_norm_le_iff _ _).mp hb v
  rw [normAtPlace_smul, abs_of_pos (inv_pos.mpr hP), normAtPlace_apply] at hp
  have hh := mul_le_mul_of_nonneg_left hp hP.le
  rw [← mul_assoc, mul_inv_cancel₀ hP.ne', one_mul] at hh
  exact hh.trans (by nlinarith [le_max_right (1:ℝ) A])

#print axioms finite_sum_common_translate
#print axioms translatedUnion_place_bound
#print axioms compact_support_place_bound
end WaringSiegel.WSL3
