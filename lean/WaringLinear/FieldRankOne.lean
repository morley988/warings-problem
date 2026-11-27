import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Determinant spacing over the infinite places

An anisotropic box of sufficiently small product contains only one
field slope. The norm gap comes from the integral determinant after
clearing the (fixed) fractional denominator. Complex places carry
multiplicity two throughout. -/
noncomputable section
open NumberField NumberField.InfinitePlace
open scoped BigOperators NumberField
namespace WaringLinear.LatticePacking
variable {K : Type*} [Field K] [NumberField K]

private theorem determinant_arch_le (α d d' c c' : ℂ) (D E : ℝ)
    (hD : 0≤D) (_hE : 0≤E) (hd : ‖d‖≤D) (hd' : ‖d'‖≤D)
    (hc : ‖α*d-c‖≤E) (hc' : ‖α*d'-c'‖≤E) : ‖d*c'-d'*c‖≤2*D*E := by
  have he : d*c'-d'*c=d'*(α*d-c)-d*(α*d'-c') := by ring
  rw [he]
  calc
    _ ≤ ‖d'*(α*d-c)‖+‖d*(α*d'-c')‖ := norm_sub_le _ _
    _ = ‖d'‖*‖α*d-c‖+‖d‖*‖α*d'-c'‖ := by rw [norm_mul,norm_mul]
    _ ≤ D*E+D*E := add_le_add (mul_le_mul hd' hc (norm_nonneg _) hD) (mul_le_mul hd hc' (norm_nonneg _) hD)
    _ = _ := by ring

private theorem abs_norm_int_ge_one {x : 𝓞 K} (hx : x≠0) :
    (1:ℝ)≤|Algebra.norm ℚ (x:K)| := by
  rw [← Algebra.coe_norm_int, ← Int.cast_one, ← Int.cast_abs, Rat.cast_intCast, Int.cast_le]
  exact Int.one_le_abs (Algebra.norm_ne_zero_iff.mpr hx)

/-- The archimedean errors may have arbitrary shapes at each embedding. -/
theorem small_box_det_zero {ι : Type*} (d c : ι → 𝓞 K)
    (α : InfinitePlace K → ℂ) (D E : InfinitePlace K → ℝ)
    (hD : ∀ w, 0≤D w) (hE : ∀ w, 0≤E w)
    (hd : ∀ i w, ‖w.embedding (d i : K)‖≤D w)
    (herr : ∀ i w, ‖α w*w.embedding (d i : K)-w.embedding (c i : K)‖≤E w)
    (hvol : (∏ w, (2*D w*E w)^(mult w))<1) (i j : ι) :
    d i*c j-d j*c i = 0 := by
  classical
  let δ : 𝓞 K := d i*c j-d j*c i
  by_contra! hne
  have hlow := abs_norm_int_ge_one (K:=K) (x:=δ) hne
  rw [← InfinitePlace.prod_eq_abs_norm] at hlow
  have hupper : (∏ w : InfinitePlace K, w (δ:K)^mult w)≤∏ w,(2*D w*E w)^mult w := by
    apply Finset.prod_le_prod
    · intro w _
      exact pow_nonneg (apply_nonneg _ _) _
    · intro w _
      apply pow_le_pow_left₀ (apply_nonneg _ _)
      rw [← norm_embedding_eq]
      simpa [δ,map_sub,map_mul] using determinant_arch_le (α w)
        (w.embedding (d i:K)) (w.embedding (d j:K))
        (w.embedding (c i:K)) (w.embedding (c j:K)) (D w) (E w)
        (hD w) (hE w) (hd i w) (hd j w) (herr i w) (herr j w)
  exact (not_lt_of_ge (hlow.trans hupper)) hvol

/-- After clearing a common denominator, the condition for all points
to have a common slope is an explicit product over the infinite places.
Here the original second coordinates are cᵢ/b, and α is the original
frequency. -/
theorem common_slope_of_small_box {ι : Type*} (d c : ι → 𝓞 K) (b : K) (hb : b≠0)
    (α : InfinitePlace K → ℂ) (D E : InfinitePlace K → ℝ)
    (hD : ∀ w, 0≤D w) (hE : ∀ w, 0≤E w)
    (hd : ∀ i w, ‖w.embedding (d i:K)‖≤D w)
    (herr : ∀ i w, ‖α w*w.embedding (d i:K)-w.embedding ((c i:K)/b)‖≤E w)
    (hvol : (∏ w, (2*D w*(w b*E w))^mult w)<1) :
    (∀ i, d i=0) ∨ ∃ γ : K, ∀ i, (c i:K)/b=γ*(d i:K) := by
  classical
  by_cases allzero : ∀ i, d i=0
  · exact Or.inl allzero
  right
  obtain ⟨i,hi⟩ := not_forall.mp allzero
  have hi' : (d i:K)≠0 := (Subalgebra.coe_eq_zero _).not.mpr hi
  have hb' (w : InfinitePlace K) : w.embedding b≠0 := (map_ne_zero _).mpr hb
  have hbound (i : ι) (w : InfinitePlace K) :
      ‖(w.embedding b*α w)*w.embedding (d i:K)-w.embedding (c i:K)‖≤w b*E w := by
    have he : (w.embedding b*α w)*w.embedding (d i:K)-w.embedding (c i:K)=
        w.embedding b*(α w*w.embedding (d i:K)-w.embedding ((c i:K)/b)) := by
      rw [map_div₀];field_simp [hb' w]
    rw [he,norm_mul,norm_embedding_eq]
    exact mul_le_mul_of_nonneg_left (herr i w) (apply_nonneg _ _)
  refine ⟨(c i:K)/(b*(d i:K)),?_⟩
  intro j
  have he := small_box_det_zero d c (fun w => w.embedding b*α w) D
    (fun w => w b*E w) hD (fun w => mul_nonneg (apply_nonneg _ _) (hE w)) hd hbound hvol i j
  have hcross : (d i:K)*(c j:K)-(d j:K)*(c i:K)=0 := by exact_mod_cast he
  field_simp
  linear_combination hcross

/-- The denominator contributes its absolute norm once, regardless of signature. -/
theorem arch_determinant_product (b : K) (D E : ℝ) :
    (∏ w : InfinitePlace K, (2*D*(w b*E))^mult w)=
      (2*D*E)^(Module.finrank ℚ K)*|Algebra.norm ℚ b| := by
  classical
  have he (w : InfinitePlace K) : 2*D*(w b*E)=2*D*E*(w b) := by ring
  calc
    _ = ∏ w : InfinitePlace K, (2*D*E)^mult w*(w b)^mult w := by
      apply Finset.prod_congr rfl
      intro w _
      rw [he,mul_pow]
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,InfinitePlace.sum_mult_eq,
      InfinitePlace.prod_eq_abs_norm]

/-- For a marked block X^θ and an inner block X^(1−θ), the determinant
volume lies below one at every sufficiently large scale when θ<1/2.
The constant can contain the fixed field denominator and box dilations. -/
theorem eventually_rank_one_threshold (C θ : ℝ) {k : ℕ} (hk : 0<k) (hθ : θ<1/2) :
    ∀ᶠ X : ℝ in Filter.atTop, C*X^((2*θ-1)*(k:ℝ))<1 := by
  have hp : 0 < (1-2*θ)*(k:ℝ) := mul_pos (by linarith) (by exact_mod_cast hk)
  have hh := tendsto_rpow_neg_atTop hp
  have he' : -((1-2*θ)*(k:ℝ))=(2*θ-1)*(k:ℝ) := by ring
  rw [he'] at hh
  have h := tendsto_const_nhds.mul hh (a:=C)
  have hh' : Filter.Tendsto (fun X : ℝ => C*X^((2*θ-1)*(k:ℝ))) Filter.atTop (nhds 0) := by simpa using h
  exact (Filter.Tendsto.eventually_lt_const (by norm_num : (0:ℝ)<1) hh')

#print axioms arch_determinant_product
#print axioms eventually_rank_one_threshold
#print axioms small_box_det_zero
#print axioms common_slope_of_small_box
end WaringLinear.LatticePacking
