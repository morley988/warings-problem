import WaringSiegel.WSL3MomentInsertionGrowth

/-!
# Generalized number-field Hua moments

For every 1 <= r <= k, the actual degree-k moment of order r(r+1)
is bounded by X^(r^2+epsilon), uniformly for bounded complex weights.
The sparse critical theorem and the entire lower-coordinate insertion
argument are proved in this project.
-/

noncomputable section
open MeasureTheory GafniTao
open scoped BigOperators Classical NumberField

namespace WaringSiegel.WSL3
open WSL2

variable {K : Type*} [Field K] [NumberField K]

theorem twice_wooleyTriangular (r : ℕ) : 2*wooleyTriangular r = r*(r+1) := by
  have h : (2 : ℝ)*wooleyTriangular r = (r : ℝ)*((r : ℝ)+1) := by
    rw [wooleyTriangular_cast]
    ring
  exact_mod_cast h

theorem numberField_generalized_hua_succ_moment_bound (k R : ℕ) (hRk : R+1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α]
      (nodes : α → 𝓞 K), Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ (w : α → ℂ) (W : ℝ), 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖^((R+1)*(R+2))
        ∂latticeHaar) ≤ C*(P^Module.finrank ℚ K : ℝ)^(((R+1)^2 : ℕ)+ε)*W^((R+1)*(R+2)) := by
  obtain ⟨A,hA,henergy⟩ := numberField_sparse_critical_energy_bound
    (K := K) k (R+1) (by omega) hRk hε
  let d := Module.finrank ℚ K
  let s := wooleyTriangular (R+1)
  have hs : 1 ≤ s := (wooleyTriangular_mono (show 1 ≤ R+1 by omega)).trans' (by norm_num [wooleyTriangular])
  let CS : ℝ := 2*(3 : ℝ)^d
  let B : ℝ := CS*(2*(s : ℝ))^d
  have hCS : 0 < CS := by dsimp [CS]; positivity
  have hB : 0 < B := by
    have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    dsimp [B]
    positivity
  refine ⟨B^R*A*CS^s,by positivity,?_⟩
  intro P hP α inst nodes hinj hbox w W hW hw
  let X : ℝ := P^d
  have hPpos : 0 < P := by linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hN : (Fintype.card α : ℝ) ≤ CS*X := by
    have h := integer_box_card_bound (Finset.univ.image nodes) P hP (by
      intro x hx v
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      exact hbox a v)
    simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using h
  have hE : weightedSystemEnergy s (fun x => sparseValue k (R+1) (nodes x)) (fun _ => 1) ≤
      A*X^ε*(Fintype.card α : ℝ)^s := by
    simpa only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
      henergy P hP nodes hinj hbox (fun _ => 1) (fun _ => zero_le_one)
  have hD := lowerPowerDifference_product_card_bound nodes hP hbox R s hs
  have hins := sparse_insertion_bound (integerCoordinates K) (integerCoordinates_injective K)
    nodes k R s
  have hu : (∫ θ, ‖frequencySum (fun x => integerCoordinates K (nodes x^k))
      (fun _ => 1) θ‖^(2*s) ∂latticeHaar) ≤
      (B^R*A*CS^s)*X^(((R+1)^2 : ℕ)+ε) := by
    rw [integral_norm_frequencySum_even_one]
    simp only [← map_sum]
    calc
      _ ≤ (∏ j : Fin R, ((powerDifferenceImage nodes (j.val+1) s).card : ℝ)) *
          weightedSystemEnergy s (fun x => sparseValue k (R+1) (nodes x)) (fun _ => 1) := hins
      _ ≤ (B^R*X^wooleyTriangular R)*(A*X^ε*(Fintype.card α : ℝ)^s) := by
        exact mul_le_mul hD hE (weightedSystemEnergy_nonneg _ _ _ (fun _ => zero_le_one))
          (by positivity)
      _ ≤ (B^R*X^wooleyTriangular R)*(A*X^ε*(CS*X)^s) := by gcongr
      _ = (B^R*A*CS^s)*(X^(wooleyTriangular R+s)*X^ε) := by
        rw [mul_pow, pow_add]
        ring
      _ = _ := by
        rw [show wooleyTriangular R+s = (R+1)^2 from triangular_add_succ_triangular R,
          ← Real.rpow_natCast X, ← Real.rpow_add hX]
  have hp : 2*s = (R+1)*(R+2) := twice_wooleyTriangular (R+1)
  change (∫ θ, ‖frequencySum (fun x => integerCoordinates K (nodes x^k)) w θ‖^((R+1)*(R+2))
    ∂latticeHaar) ≤ _
  calc
    _ ≤ W^((R+1)*(R+2)) * (∫ θ, ‖frequencySum (fun x => integerCoordinates K (nodes x^k))
        (fun _ => 1) θ‖^((R+1)*(R+2)) ∂latticeHaar) := by
      simpa only [hp] using integral_norm_frequencySum_even_le_unweighted
        (fun x => integerCoordinates K (nodes x^k)) w s W hW hw
    _ ≤ W^((R+1)*(R+2)) * ((B^R*A*CS^s)*X^(((R+1)^2 : ℕ)+ε)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [hp] using hu
    _ = _ := by ring

theorem numberField_generalized_hua_moment_bound (k r : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ {α : Type*} [Fintype α]
      (nodes : α → 𝓞 K), Function.Injective nodes →
      (∀ x, ∀ v : NumberField.InfinitePlace K, v (nodes x : K) ≤ P) →
      ∀ (w : α → ℂ) (W : ℝ), 0 ≤ W → (∀ x, ‖w x‖ ≤ W) →
      (∫ θ, ‖finiteWeylSum (integerCoordinates K) k nodes w θ‖^(r*(r+1))
        ∂latticeHaar) ≤ C*(P^Module.finrank ℚ K : ℝ)^((r^2 : ℕ)+ε)*W^(r*(r+1)) := by
  cases r with
  | zero => omega
  | succ R => exact numberField_generalized_hua_succ_moment_bound k R hrk hε

#print axioms numberField_generalized_hua_moment_bound

end WaringSiegel.WSL3
