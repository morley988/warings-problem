import WaringSiegel.WSL3MomentHuaWeighted
import WaringSiegel.WSL3MomentSystemPartition

/-!
# Pointwise insertion of lower coefficients

Grouping the tuple frequencies and Cauchy--Schwarz inserts any finite
frequency system into an even pointwise moment. The exact cost is the
number of distinct tuple sums, and coefficients remain arbitrary complex.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

variable {ι α : Type*} [Fintype ι] [Fintype α]

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

theorem frequencySum_group_fibers {β : Type*} [Fintype β]
    (tag : α → β) (label : β → ι → ℤ) (w : α → ℂ)
    (θ : ι → AddCircle (1 : ℝ)) :
    frequencySum (fun x => label (tag x)) w θ =
      frequencySum label (fun b => ∑ x : {x // tag x=b}, w x) θ := by
  have h := sum_fibers_eq tag (fun x => w x * latticeCharacter (label (tag x)) θ)
  calc
    _ = ∑ b, ∑ x : {x // tag x=b}, w x * latticeCharacter (label (tag x)) θ := h.symm
    _ = _ := by
      unfold frequencySum
      apply Finset.sum_congr rfl
      intro b hb
      simp only [show ∀ x : {x // tag x=b}, tag x=b from fun x => x.property,
        Finset.sum_mul]

theorem norm_sum_sq_le_frequency_moment (v : α → ι → ℤ) (w : α → ℂ) :
    ‖∑ x, w x‖^2 ≤ ((Finset.univ.image v).card : ℝ) *
      (∫ θ, ‖frequencySum v w θ‖^2 ∂latticeHaar) := by
  letI : DecidableEq (Finset.univ.image v) := Classical.decEq _
  let tag : α → Finset.univ.image v := fun x =>
    ⟨v x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
  let bweight (b : Finset.univ.image v) : ℂ := ∑ x : {x // tag x=b}, w x
  have hf (θ : ι → AddCircle (1 : ℝ)) : frequencySum v w θ =
      frequencySum (fun b : Finset.univ.image v => (b : ι → ℤ)) bweight θ :=
    frequencySum_group_fibers tag (fun b : Finset.univ.image v => (b : ι → ℤ)) w θ
  have hsum : (∑ x, w x) = ∑ b, bweight b := by
    have h := hf 0
    simpa only [frequencySum, latticeCharacter, Pi.zero_apply, fourier_eval_zero,
      Finset.prod_const_one, mul_one] using h
  have hint : (∫ θ, ‖frequencySum v w θ‖^2 ∂latticeHaar) = ∑ b, ‖bweight b‖^2 := by
    simp_rw [hf]
    rw [integral_norm_frequencySum_sq]
    simp only [Fintype.sum_prod_type, Subtype.val_inj]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hsum, hint]
  calc
    _ ≤ (∑ b, ‖bweight b‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ ≤ _ := by
      simpa only [Finset.card_univ, Fintype.card_coe, one_mul, one_pow,
        Finset.sum_const, nsmul_eq_mul, mul_one] using
        Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Finset.univ.image v))
          (fun _ => (1 : ℝ)) (fun b => ‖bweight b‖)

theorem norm_sum_even_le_inserted_moment (v : α → ι → ℤ) (w : α → ℂ) (s : ℕ) :
    ‖∑ x, w x‖^(2*s) ≤
      ((Finset.univ.image (fun x : Fin s → α => ∑ i, v (x i))).card : ℝ) *
        (∫ θ, ‖frequencySum v w θ‖^(2*s) ∂latticeHaar) := by
  have h := norm_sum_sq_le_frequency_moment (fun x : Fin s → α => ∑ i, v (x i))
    (fun x => ∏ i, w (x i))
  have hp (θ : ι → AddCircle (1 : ℝ)) :
      ‖frequencySum (fun x : Fin s → α => ∑ i, v (x i)) (fun x => ∏ i, w (x i)) θ‖^2 =
        ‖frequencySum v w θ‖^(2*s) := by
    rw [← frequencySum_pow, norm_pow, ← pow_mul, Nat.mul_comm s]
  simpa only [← Fintype.sum_pow, norm_pow, ← pow_mul, Nat.mul_comm s, hp] using h

#print axioms norm_sum_even_le_inserted_moment

end WaringSiegel.WSL3
