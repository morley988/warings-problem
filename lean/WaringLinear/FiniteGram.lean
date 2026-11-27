import WaringSiegel.WSL2MomentKernelAverage
import WaringSiegel.WSL3MomentSystemPartition

/-! # The small-conductor Gram bound on finite abelian groups

For a sampled residue function v whose fibres have cardinality at most M,
the restriction of any family of distinct characters has squared operator
norm at most M times the order of the residue group.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open WaringSiegel.WSL2 WaringSiegel.WSL3

namespace WaringLinear
variable {G J X : Type*} [AddCommGroup G] [Fintype G] [Fintype J] [Fintype X]

/-- Orthogonality with an arbitrary choice of distinct characters. -/
theorem character_synthesis_plancherel (χ : J → AddChar G ℂ) (hχ : Function.Injective χ)
    (w : J → ℂ) :
    (∑ b : G, ‖∑ j, w j * χ j b‖^2) =
      (Fintype.card G : ℝ) * ∑ j, ‖w j‖^2 := by
  have he := finite_character_family_average_energy χ w AddChar.doubleDualEmb
    (fun φ => AddChar.expect_eq_ite φ)
  change (𝔼 b : G, ‖∑ j, w j * χ j b‖^2) = _ at he
  have hdiag (p : J × J) : χ p.1 = χ p.2 ↔ p.1 = p.2 := hχ.eq_iff
  simp_rw [hdiag] at he
  simp only [Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re] at he
  rw [Fintype.expect_eq_sum_div_card] at he
  have hg : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simpa only [mul_comm] using (div_eq_iff hg).mp he

/-- Finite large sieve for the rows sampled at v(x). The occupancy condition
only counts equal residues and makes no injectivity assumption on the sample. -/
theorem sampled_character_synthesis (v : X → G) (M : ℕ)
    (hM : ∀ b, Nat.card {x : X // v x=b} ≤ M)
    (χ : J → AddChar G ℂ) (hχ : Function.Injective χ) (w : J → ℂ) :
    (∑ x, ‖∑ j, w j * χ j (v x)‖^2) ≤
      (M : ℝ) * Fintype.card G * ∑ j, ‖w j‖^2 := by
  let F (b : G) := ‖∑ j, w j * χ j b‖^2
  have hpartition : (∑ x, F (v x)) = ∑ b : G, (Nat.card {x : X // v x=b} : ℝ)*F b := by
    rw [← sum_fibers_eq v (fun x => F (v x))]
    apply Finset.sum_congr rfl
    intro b _
    simp only [show ∀ x : {x : X // v x=b}, v x.val = b from fun x => x.property,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  change (∑ x, F (v x)) ≤ _
  rw [hpartition, mul_assoc, ← character_synthesis_plancherel χ hχ w, Finset.mul_sum]
  exact Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_right
    (by exact_mod_cast hM b) (sq_nonneg _))

#print axioms sampled_character_synthesis

end WaringLinear
