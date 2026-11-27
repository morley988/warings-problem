import WaringSiegel.WSL3MomentSystemEnergy

/-!
# The native theorem for literal arbitrary p-spaced systems

The native global mean is identified with its exact weighted equation
energy. Constants are uniform over every polynomial system in Phi_tau,
every finite label set, and every nonnegative coefficient family.
-/

noncomputable section
open Finset GafniTao
open scoped BigOperators ComplexConjugate Classical
namespace WaringSiegel.WSL3
open WSL2
variable {α : Type*} [Fintype α]

theorem weightedIntegerSource_system_mean (q k s : ℕ) [NeZero q]
    (φ : WooleyPolynomialSystem k) (labels : α ↪ ℤ) (w : α → ℝ) (hmass : (∑ x, w x ^ 2) ≠ 0) :
    wooleySourcePolynomialMean s q φ
      (weightedIntegerSource labels (fun x => (w x : ℂ))) =
      weightedSystemEnergy s (fun x j => (((φ j).eval (labels x) : ℤ) : ZMod q)) w /
        (∑ x, w x ^ 2) ^ s := by
  let γ := weightedIntegerSource labels (fun x => (w x : ℂ))
  have hγ : wooleySourceMassSq γ ≠ 0 := by
    simpa only [γ, weightedIntegerSource_real_mass] using hmass
  have hsum (a : Fin k → ZMod q) :
      wooleySourcePolynomialSum φ γ a =
        ∑ x, (w x : ℂ) * ZMod.stdAddChar
          (∑ j : Fin k, a j * (((φ j).eval (labels x) : ℤ) : ZMod q)) := by
    rw [wooleySourcePolynomialSum,
      weightedIntegerSource_sum labels (fun x => (w x : ℂ))
        (fun n z => z * wooleySourcePolynomialPhase φ a n)
        (by simp)]
    rfl
  change wooleySourcePolynomialMean s q φ γ = _
  unfold wooleySourcePolynomialMean
  simp_rw [norm_wooleySourceNormalizedPolynomialSum_pow_even _ γ _ s hγ, hsum]
  rw [← Finset.mul_sum]
  calc
    _ = (wooleySourceMassSq γ)⁻¹ ^ s *
      (((q ^ k : ℕ) : ℝ)⁻¹ * ∑ a : Fin k → ZMod q,
        ‖∑ x, (w x : ℂ) * ZMod.stdAddChar
          (∑ j : Fin k, a j * (((φ j).eval (labels x) : ℤ) : ZMod q))‖ ^ (2 * s)) := by ring
    _ = _ := by
      rw [weighted_system_grid_mean, weightedIntegerSource_real_mass, inv_pow]
      ring

theorem native_system_modular_energy_bound_of_bounded (k p : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (H : ℕ) (φ : WooleyPolynomialSystem k), φ.InPhiTau p (k*H) τ → ∀ {α : Type*} [Fintype α] (labels : α → ℤ), B0 ≤ k * H →
        Function.Injective (fun x => (labels x : ZMod (p ^ H))) →
        ∀ w : α → ℝ, (∀ x, 0 ≤ w x) → (∀ x, w x ≤ 1) →
        weightedSystemEnergy (wooleyTriangular k)
          (fun x j => (((φ j).eval (labels x) : ℤ) : ZMod (p ^ (k * H)))) w ≤
          C * (p ^ (k * H) : ℝ) ^ δ * (∑ x, w x ^ 2) ^ (wooleyTriangular k) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨C, hC, B0, hmain⟩ := wooleyPolynomialCorollary32_native
    k p hp hk hkp τ δ hτ hδ
  refine ⟨C, hC, B0, ?_⟩
  intro H φ hPhi α inst labels hB hinj w hw0 hw1
  have hs : 1 ≤ wooleyTriangular k := by
    simp only [wooleyTriangular]
    have : 2 ≤ k * (k + 1) := by nlinarith
    omega
  have hM0 : 0 ≤ ∑ x, w x ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hM : (∑ x, w x ^ 2) = 0
  · have hwzero : ∀ x, w x = 0 := by
      intro x
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => sq_nonneg (w x))).mp hM x (Finset.mem_univ _)
      exact sq_eq_zero_iff.mp h
    letI : Nonempty (Fin (wooleyTriangular k)) := ⟨⟨0, hs⟩⟩
    simp [weightedSystemEnergy, hwzero, Nat.ne_of_gt hs]
  · let e : α ↪ ℤ := ⟨labels, fun x y h => hinj (congrArg (fun n : ℤ => (n : ZMod (p ^ H))) h)⟩
    let γ := weightedIntegerSource e (fun x => (w x : ℂ))
    have hγ : wooleySourceMassSq γ ≠ 0 := by
      simpa only [γ, weightedIntegerSource_real_mass] using hM
    have hadm : γ.Admissible := weightedIntegerSource_admissible e _ (by
      intro x
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x)] using hw1 x)
    have hres : Set.InjOn (fun n : ℤ => (n : ZMod (p ^ H))) γ.support :=
      weightedIntegerSource_residue_injective e _ _ hinj
    have hbound := hmain (k * H) φ γ hB hPhi hadm
    simp only [wooley_mul_ceilDiv_self hk] at hbound
    rw [source_conditioned_mean_of_residue_injective _ _ _ _ γ hγ hres,
      weightedIntegerSource_system_mean _ _ _ φ e w hM, mul_one] at hbound
    exact (div_le_iff₀ (pow_pos (lt_of_le_of_ne hM0 (Ne.symm hM)) _)).mp hbound

theorem native_system_modular_energy_bound (k p : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (H : ℕ) (φ : WooleyPolynomialSystem k), φ.InPhiTau p (k*H) τ → ∀ {α : Type*} [Fintype α] (labels : α → ℤ), B0 ≤ k * H →
        Function.Injective (fun x => (labels x : ZMod (p ^ H))) →
        ∀ w : α → ℝ, (∀ x, 0 ≤ w x) →
        weightedSystemEnergy (wooleyTriangular k)
          (fun x j => (((φ j).eval (labels x) : ℤ) : ZMod (p ^ (k * H)))) w ≤
          C * (p ^ (k * H) : ℝ) ^ δ * (∑ x, w x ^ 2) ^ (wooleyTriangular k) := by
  obtain ⟨C, hC, B0, hmain⟩ := native_system_modular_energy_bound_of_bounded k p hp hk hkp hτ hδ
  refine ⟨C, hC, B0, ?_⟩
  intro H φ hPhi α inst labels hB hinj w hw
  let M : ℝ := 1 + ∑ x, w x
  have hM : 0 < M := by
    have hsum : 0 ≤ ∑ x, w x := Finset.sum_nonneg (fun x _ => hw x)
    dsimp [M]
    linarith
  have hwM (x : α) : w x ≤ M := by
    have h := Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ x)
    dsimp [M]
    linarith
  have hb := hmain H φ hPhi labels hB hinj (fun x => M⁻¹ * w x)
    (fun x => mul_nonneg (inv_nonneg.mpr hM.le) (hw x))
    (fun x => by
      calc
        M⁻¹ * w x ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hwM x) (inv_nonneg.mpr hM.le)
        _ = 1 := inv_mul_cancel₀ hM.ne')
  rw [weightedSystemEnergy_mul] at hb
  have hmass : (∑ x, (M⁻¹ * w x) ^ 2) ^ (wooleyTriangular k) =
      M⁻¹ ^ (2 * wooleyTriangular k) * (∑ x, w x ^ 2) ^ (wooleyTriangular k) := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, mul_pow, ← pow_mul]
  rw [hmass] at hb
  have hpos : 0 < M⁻¹ ^ (2 * wooleyTriangular k) := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    _ ≤ _ := hb
    _ = _ := by ring


#print axioms native_system_modular_energy_bound

end WaringSiegel.WSL3
