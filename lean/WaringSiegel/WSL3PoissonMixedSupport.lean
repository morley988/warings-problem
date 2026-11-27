import WaringSiegel.WSL3PoissonCompactLinear
import WaringSiegel.WSL2MomentCubicWeyl

/-! # Actual finite lattice support and exact correlation domains -/
noncomputable section
open Function NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ComplexConjugate
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compact_integer_support_finite {f : mixedSpace K → ℂ}
    (hf : HasCompactSupport f) (P : ℝ) (hP : P ≠ 0) :
    (support (fun x : 𝓞 K => f (P⁻¹ • mixedEmbedding K (x:K)))).Finite := by
  let g : 𝓞 K → mixedSpace K := fun x => mixedEmbedding K (x:K)
  let B : Set (mixedSpace K) := (fun x : mixedSpace K => P • x) '' tsupport f
  have hB : IsCompact B := hf.image (by fun_prop)
  have hfin := ZSpan.setFinite_inter (NumberField.mixedEmbedding.latticeBasis K) hB.isBounded
  have himg : (g '' support (fun x : 𝓞 K => f (P⁻¹ • g x))).Finite := by
    apply hfin.subset
    rintro z ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨P⁻¹ • g x, subset_closure hx, ?_⟩
      simp only [smul_smul, mul_inv_cancel₀ hP, one_smul]
    · rw [NumberField.mixedEmbedding.span_latticeBasis]
      exact ⟨x, rfl⟩
  apply himg.of_finite_image
  intro x hx y hy h
  exact (FaithfulSMul.algebraMap_injective (𝓞 K) K) ((mixedEmbedding K).injective h)

def compactIntegerSupport (f : mixedSpace K → ℂ) (hf : HasCompactSupport f)
    (P : ℝ) (hP : P ≠ 0) : Finset (𝓞 K) :=
  (compact_integer_support_finite hf P hP).toFinset

@[simp] theorem mem_compactIntegerSupport (f : mixedSpace K → ℂ) (hf : HasCompactSupport f)
    (P : ℝ) (hP : P ≠ 0) (x : 𝓞 K) :
    x ∈ compactIntegerSupport f hf P hP ↔ f (P⁻¹ • mixedEmbedding K (x:K)) ≠ 0 := by
  simp only [compactIntegerSupport, Set.Finite.mem_toFinset, mem_support]

section Additive
variable {G : Type*} [AddCommGroup G]

theorem shiftedWeight_support_overlap {w : G → ℂ} {S : Finset G}
    (hw : ∀ x, w x ≠ 0 → x ∈ S) (h : G) :
    support (shiftedWeight w h) ⊆ (additiveOverlap S h : Set G) := by
  intro x hx
  obtain ⟨hxph, hxconj⟩ := mul_ne_zero_iff.mp hx
  have hx0 : w x ≠ 0 := by intro hz; exact hxconj (by rw [hz, map_zero])
  exact Finset.mem_filter.mpr ⟨hw x hx0, hw (x+h) hxph⟩

theorem doubleShiftedWeight_support_overlap {w : G → ℂ} {S : Finset G}
    (hw : ∀ x, w x ≠ 0 → x ∈ S) (h j : G) :
    support (doubleShiftedWeight w h j) ⊆
      (additiveOverlap (additiveOverlap S h) j : Set G) :=
  shiftedWeight_support_overlap (fun x hx => shiftedWeight_support_overlap hw h hx) j

theorem sum_shiftedWeight_eq_tsum {w : G → ℂ} {S : Finset G}
    (hw : ∀ x, w x ≠ 0 → x ∈ S) (h : G) (χ : G → ℂ) :
    (∑ x ∈ additiveOverlap S h, shiftedWeight w h x * χ x) =
      ∑' x : G, shiftedWeight w h x * χ x := by
  symm
  apply tsum_eq_sum
  intro x hx
  have hz : shiftedWeight w h x = 0 := by
    by_contra hn
    exact hx (shiftedWeight_support_overlap hw h hn)
  rw [hz, zero_mul]

theorem sum_doubleShiftedWeight_eq_tsum {w : G → ℂ} {S : Finset G}
    (hw : ∀ x, w x ≠ 0 → x ∈ S) (h j : G) (χ : G → ℂ) :
    (∑ x ∈ additiveOverlap (additiveOverlap S h) j, doubleShiftedWeight w h j x * χ x) =
      ∑' x : G, doubleShiftedWeight w h j x * χ x := by
  symm
  apply tsum_eq_sum
  intro x hx
  have hz : doubleShiftedWeight w h j x = 0 := by
    by_contra hn
    exact hx (doubleShiftedWeight_support_overlap hw h j hn)
  rw [hz, zero_mul]
end Additive
end WaringSiegel.WSL3Poisson
