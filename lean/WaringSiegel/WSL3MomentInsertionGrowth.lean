import WaringSiegel.WSL3MomentSparseInsertion

/-!
# Sharp box cost for inserting lower power-sum equations

The exact lower-coordinate insertion costs X^(1+...+R), with constants
uniform in the box size and in every injective finite indexing of its nodes.
-/

noncomputable section
open MeasureTheory GafniTao
open scoped BigOperators Classical NumberField

namespace WaringSiegel.WSL3
open WSL2

variable {K : Type*} [Field K] [NumberField K]
variable {α : Type*} [Fintype α]

theorem place_indexed_sum_power_le (nodes : α → 𝓞 K) {P : ℝ} (hP : 0 ≤ P)
    (hbox : ∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P)
    (j s : ℕ) (x : Fin s → α) (v : NumberField.InfinitePlace K) :
    v (((∑ i, nodes (x i)^j : 𝓞 K) : K)) ≤ (s : ℝ)*P^j := by
  simp only [map_sum, map_pow]
  calc
    v (∑ i, (nodes (x i) : K)^j) ≤ ∑ i, v ((nodes (x i) : K)^j) :=
      v.val.sum_le Finset.univ _
    _ ≤ ∑ _i : Fin s, P^j := by
      apply Finset.sum_le_sum
      intro i hi
      rw [map_pow]
      exact pow_le_pow_left₀ (apply_nonneg v _) (hbox _ v) j
    _ = _ := by simp

theorem powerDifferenceImage_card_bound (nodes : α → 𝓞 K) {P : ℝ} (hP : 1 ≤ P)
    (hbox : ∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P)
    (j s : ℕ) (hs : 1 ≤ s) :
    ((powerDifferenceImage nodes j s).card : ℝ) ≤
      (2 * (3 : ℝ)^Module.finrank ℚ K * (2*(s : ℝ))^Module.finrank ℚ K) *
        (P^Module.finrank ℚ K)^j := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hR : 1 ≤ 2*(s : ℝ)*P^j := by
    have hpj := one_le_pow₀ hP (n := j)
    nlinarith
  have h := integer_box_card_bound (powerDifferenceImage nodes j s) (2*s*P^j) hR (by
    intro a ha v
    obtain ⟨xy,hxy,rfl⟩ := Finset.mem_image.mp ha
    have hb := place_sub_le_twice
      (place_indexed_sum_power_le nodes (by linarith) hbox j s xy.1)
      (place_indexed_sum_power_le nodes (by linarith) hbox j s xy.2) v
    simpa only [mul_assoc] using hb)
  convert h using 1
  simp only [mul_pow, ← pow_mul, Nat.mul_comm j (Module.finrank ℚ K)]
  ring

theorem sum_fin_succ_eq_triangular (R : ℕ) :
    (∑ j : Fin R, (j.val+1)) = wooleyTriangular R := by
  induction R with
  | zero => simp [wooleyTriangular]
  | succ R ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, ih]
    have h : (wooleyTriangular R : ℝ) + ((R : ℝ)+1) = wooleyTriangular (R+1) := by
      rw [wooleyTriangular_cast, wooleyTriangular_cast]
      push_cast
      ring
    exact_mod_cast h

theorem triangular_add_succ_triangular (R : ℕ) :
    wooleyTriangular R + wooleyTriangular (R+1) = (R+1)^2 := by
  have h : (wooleyTriangular R : ℝ) + wooleyTriangular (R+1) = ((R : ℝ)+1)^2 := by
    rw [wooleyTriangular_cast, wooleyTriangular_cast]
    push_cast
    ring
  exact_mod_cast h

theorem lowerPowerDifference_product_card_bound (nodes : α → 𝓞 K) {P : ℝ} (hP : 1 ≤ P)
    (hbox : ∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P)
    (R s : ℕ) (hs : 1 ≤ s) :
    (∏ j : Fin R, ((powerDifferenceImage nodes (j.val+1) s).card : ℝ)) ≤
      (2 * (3 : ℝ)^Module.finrank ℚ K * (2*(s : ℝ))^Module.finrank ℚ K)^R *
        (P^Module.finrank ℚ K)^wooleyTriangular R := by
  calc
    _ ≤ ∏ j : Fin R, (2 * (3 : ℝ)^Module.finrank ℚ K *
        (2*(s : ℝ))^Module.finrank ℚ K) * (P^Module.finrank ℚ K)^(j.val+1) :=
      Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _) (fun j _ =>
        powerDifferenceImage_card_bound nodes hP hbox (j.val+1) s hs)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum, sum_fin_succ_eq_triangular]

#print axioms lowerPowerDifference_product_card_bound

end WaringSiegel.WSL3
