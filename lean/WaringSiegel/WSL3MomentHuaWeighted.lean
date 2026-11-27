import WaringSiegel.WSL3MomentHua

/-!
# Arbitrary bounded coefficients in all number-field Hua moments

Exact finite Fourier orthogonality transfers every even unweighted moment
to complex coefficients.  There is no positivity requirement on the weights.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NumberField Classical

namespace WaringSiegel.WSL3
open WSL2

variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem integral_norm_frequencySum_even_one (v : α → ι → ℤ) (s : ℕ) :
    (∫ θ, ‖frequencySum v (fun _ => 1) θ‖^(2*s) ∂latticeHaar) =
      (frequencyEnergy (fun x : Fin s → α => ∑ i, v (x i)) : ℝ) := by
  have hn (θ : ι → AddCircle (1 : ℝ)) :
      ‖frequencySum v (fun _ => 1) θ‖^(2*s) = ‖frequencySum v (fun _ => 1) θ^s‖^2 := by
    rw [norm_pow, ← pow_mul, Nat.mul_comm]
  simp_rw [hn, frequencySum_pow, Finset.prod_const_one]
  exact integral_norm_frequencySum_sq_one _

theorem integral_norm_frequencySum_even_le_unweighted (v : α → ι → ℤ) (w : α → ℂ)
    (s : ℕ) (W : ℝ) (hW : 0 ≤ W) (hw : ∀ a, ‖w a‖ ≤ W) :
    (∫ θ, ‖frequencySum v w θ‖^(2*s) ∂latticeHaar) ≤
      W^(2*s) * (∫ θ, ‖frequencySum v (fun _ => 1) θ‖^(2*s) ∂latticeHaar) := by
  rw [integral_norm_frequencySum_even_one]
  simpa only [mul_comm] using integral_norm_frequencySum_even_le_energy v w s W hW hw

variable {K : Type*} [Field K] [NumberField K]

/-- Every classical Hua exponent, uniformly over every finite injectively
indexed number-field box and every bounded complex coefficient family. -/
theorem numberField_hua_moment_bound (k j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α],
      ∀ nodes : α → 𝓞 K, Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ w : α → ℂ, ∀ W : ℝ, 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖^(2^j) ∂latticeHaar) ≤
        C * (P ^ Module.finrank ℚ K : ℝ)^((2^j-j : ℕ)+ε) * W^(2^j) := by
  obtain ⟨C, hC, hbound⟩ := numberField_hua_moment_unweighted (K := K) k j hj hjk hε
  refine ⟨C, hC, ?_⟩
  intro P hP α inst nodes hinj hnodes w W hW hw
  have hu := hbound P hP (Finset.univ.image nodes) (by
    intro x hx v
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact hnodes a v)
  have hu' : (∫ θ, ‖frequencySum (fun x => integerCoordinates K (nodes x^k))
      (fun _ => 1) θ‖^(2^j) ∂latticeHaar) ≤
        C * (P ^ Module.finrank ℚ K : ℝ)^((2^j-j : ℕ)+ε) := by
    simpa only [frequencySum_power_eq_image nodes hinj k] using hu
  have hs : 2 * 2^(j-1) = 2^j := by rw [← pow_succ']; congr 1; omega
  change (∫ θ, ‖frequencySum (fun x => integerCoordinates K (nodes x^k)) w θ‖^(2^j)
    ∂latticeHaar) ≤ _
  calc
    _ ≤ W^(2^j) * (∫ θ, ‖frequencySum (fun x => integerCoordinates K (nodes x^k))
        (fun _ => 1) θ‖^(2^j) ∂latticeHaar) := by
      simpa only [hs] using integral_norm_frequencySum_even_le_unweighted
        (fun x => integerCoordinates K (nodes x^k)) w (2^(j-1)) W hW hw
    _ ≤ W^(2^j) * (C * (P ^ Module.finrank ℚ K : ℝ)^((2^j-j : ℕ)+ε)) :=
      mul_le_mul_of_nonneg_left hu' (by positivity)
    _ = _ := by ring

#print axioms numberField_hua_moment_bound

end WaringSiegel.WSL3
