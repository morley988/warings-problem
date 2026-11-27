import WaringSiegel.WSL3MomentPointwiseInsertion
import WaringSiegel.WSL3MomentInsertionGrowth

/-!
# Uniform pointwise lower-coefficient insertion over number fields

For arbitrary complex coefficients, inserting R lower coefficients into
an even pointwise moment costs C X^(R(R+1)/2). The constant is chosen before
all box scales, finite node index sets, and coefficient families.
-/

noncomputable section
open MeasureTheory GafniTao
open scoped BigOperators Classical NumberField

namespace WaringSiegel.WSL3
open WSL2

variable {K : Type*} [Field K] [NumberField K]
variable {α : Type*} [Fintype α]

def powerSumImage (nodes : α → 𝓞 K) (j s : ℕ) : Finset (𝓞 K) :=
  Finset.univ.image (fun x : Fin s → α => ∑ i, nodes (x i)^j)

theorem powerSumImage_card_bound (nodes : α → 𝓞 K) {P : ℝ} (hP : 1 ≤ P)
    (hbox : ∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P)
    (j s : ℕ) (hs : 1 ≤ s) :
    ((powerSumImage nodes j s).card : ℝ) ≤
      (2*(3 : ℝ)^Module.finrank ℚ K*(s : ℝ)^Module.finrank ℚ K) *
        (P^Module.finrank ℚ K)^j := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hR : 1 ≤ (s : ℝ)*P^j := one_le_mul_of_one_le_of_one_le hsR (one_le_pow₀ hP)
  have h := integer_box_card_bound (powerSumImage nodes j s) (s*P^j) hR (by
    intro a ha v
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact place_indexed_sum_power_le nodes (by linarith) hbox j s x v)
  convert h using 1
  simp only [mul_pow, ← pow_mul, Nat.mul_comm j (Module.finrank ℚ K)]
  ring

theorem lowerPowerSum_product_card_bound (nodes : α → 𝓞 K) {P : ℝ} (hP : 1 ≤ P)
    (hbox : ∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P)
    (R s : ℕ) (hs : 1 ≤ s) :
    (∏ j : Fin R, ((powerSumImage nodes (j.val+1) s).card : ℝ)) ≤
      (2*(3 : ℝ)^Module.finrank ℚ K*(s : ℝ)^Module.finrank ℚ K)^R *
        (P^Module.finrank ℚ K)^wooleyTriangular R := by
  calc
    _ ≤ ∏ j : Fin R, (2*(3 : ℝ)^Module.finrank ℚ K*(s : ℝ)^Module.finrank ℚ K) *
        (P^Module.finrank ℚ K)^(j.val+1) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun j _ =>
        powerSumImage_card_bound nodes hP hbox (j.val+1) s hs)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum, sum_fin_succ_eq_triangular]

theorem lowerFrequencyTuple_range_card_le (nodes : α → 𝓞 K) (R s : ℕ) :
    (Finset.univ.image (fun x : Fin s → α =>
      ∑ i, vinogradovFrequency (integerCoordinates K) R nodes (x i))).card ≤
      ∏ j : Fin R, (powerSumImage nodes (j.val+1) s).card := by
  let box := Fintype.piFinset (fun j : Fin R => powerSumImage nodes (j.val+1) s)
  let D := box.image (systemCoordinates (integerCoordinates K) R)
  have hi : Finset.univ.image (fun x : Fin s → α =>
      ∑ i, vinogradovFrequency (integerCoordinates K) R nodes (x i)) ⊆ D := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_image.mpr
    refine ⟨(fun j => ∑ i, nodes (x i)^(j.val+1)), ?_, ?_⟩
    · exact Fintype.mem_piFinset.mpr (fun j => Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
    · ext ji
      simp only [systemCoordinates, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        map_sum, Finset.sum_apply, vinogradovFrequency]
  exact (Finset.card_le_card hi).trans (Finset.card_image_le.trans_eq (Fintype.card_piFinset _))

/-- Pointwise insertion with its sharp number-field volume cost. No
positivity or smoothness requirement is imposed on the coefficients. -/
theorem numberField_pointwise_insertion_bound (R s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α]
      (nodes : α → 𝓞 K),
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℂ,
      ‖∑ x, w x‖^(2*s) ≤ C*(P^Module.finrank ℚ K)^wooleyTriangular R *
        (∫ θ, ‖frequencySum (vinogradovFrequency (integerCoordinates K) R nodes) w θ‖^(2*s)
          ∂latticeHaar) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0<s by omega)
  refine ⟨(2*(3 : ℝ)^Module.finrank ℚ K*(s : ℝ)^Module.finrank ℚ K)^R,
    by positivity,?_⟩
  intro P hP α inst nodes hbox w
  have hcard : ((Finset.univ.image (fun x : Fin s → α =>
      ∑ i, vinogradovFrequency (integerCoordinates K) R nodes (x i))).card : ℝ) ≤
      (2*(3 : ℝ)^Module.finrank ℚ K*(s : ℝ)^Module.finrank ℚ K)^R *
        (P^Module.finrank ℚ K)^wooleyTriangular R := by
    apply le_trans _ (lowerPowerSum_product_card_bound nodes hP hbox R s hs)
    exact_mod_cast lowerFrequencyTuple_range_card_le nodes R s
  exact (norm_sum_even_le_inserted_moment
    (vinogradovFrequency (integerCoordinates K) R nodes) w s).trans
      (mul_le_mul_of_nonneg_right hcard (integral_nonneg (fun _ => pow_nonneg (norm_nonneg _) _)))

#print axioms numberField_pointwise_insertion_bound

end WaringSiegel.WSL3
