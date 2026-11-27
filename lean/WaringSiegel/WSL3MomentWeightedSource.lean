import WaringSiegel.WSL3MomentNativeSource
import WaringSiegel.WSL3MomentWeightedMean

/-!
# Arbitrary coefficients in the native integer source

Embedding a finite coefficient family into the literal integer Finsupp
preserves its values, sums, and L2 mass.  Deep singleton residue classes
have normalized mean one even when their coefficients are unequal.
-/

noncomputable section
open Finset GafniTao
open scoped BigOperators ComplexConjugate Classical

namespace WaringSiegel.WSL3
open WSL2

variable {α : Type*} [Fintype α]

def weightedIntegerSource (labels : α ↪ ℤ) (w : α → ℂ) : WooleySourceSequence :=
  Finsupp.embDomain labels (Finsupp.equivFunOnFinite.symm w)

@[simp] theorem weightedIntegerSource_apply (labels : α ↪ ℤ) (w : α → ℂ) (x : α) :
    weightedIntegerSource labels w (labels x) = w x := by
  rw [weightedIntegerSource, Finsupp.embDomain_apply]
  rfl

theorem weightedIntegerSource_support (labels : α ↪ ℤ) (w : α → ℂ) :
    (weightedIntegerSource labels w).support =
      (Finset.univ.filter (fun x => w x ≠ 0)).map labels := by
  rw [weightedIntegerSource, Finsupp.support_embDomain]
  ext n
  simp

theorem weightedIntegerSource_sum (labels : α ↪ ℤ) (w : α → ℂ)
    {T : Type*} [AddCommMonoid T] (F : ℤ → ℂ → T) (hF : ∀ n, F n 0 = 0) :
    (∑ n ∈ (weightedIntegerSource labels w).support,
      F n (weightedIntegerSource labels w n)) = ∑ x, F (labels x) (w x) := by
  rw [weightedIntegerSource_support, Finset.sum_map]
  simp only [weightedIntegerSource_apply]
  apply Finset.sum_subset (by simp)
  intro x hx hnot
  have hw : w x = 0 := by simpa using hnot
  rw [hw, hF]

theorem weightedIntegerSource_mass (labels : α ↪ ℤ) (w : α → ℂ) :
    wooleySourceMassSq (weightedIntegerSource labels w) = ∑ x, ‖w x‖ ^ 2 :=
  weightedIntegerSource_sum labels w (fun _ z => ‖z‖ ^ 2) (by simp)

theorem weightedIntegerSource_admissible (labels : α ↪ ℤ) (w : α → ℂ)
    (hw : ∀ x, ‖w x‖ ≤ 1) : (weightedIntegerSource labels w).Admissible := by
  intro n
  by_cases hn : n ∈ (weightedIntegerSource labels w).support
  · rw [weightedIntegerSource_support] at hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hn
    simpa using hw x
  · rw [Finsupp.notMem_support_iff.mp hn]
    norm_num

theorem weightedIntegerSource_residue_injective (labels : α ↪ ℤ) (w : α → ℂ)
    (q : ℕ) (hinj : Function.Injective (fun x => (labels x : ZMod q))) :
    Set.InjOn (fun n : ℤ => (n : ZMod q)) (weightedIntegerSource labels w).support := by
  intro n hn m hm heq
  rw [weightedIntegerSource_support] at hn hm
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hn
  obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hm
  exact congrArg labels (hinj heq)

/-- Unequal nonzero coefficients cause no loss in a residue class containing
one support point: the L2 normalization cancels its coefficient norm. -/
theorem source_singleton_residue_normalized_norm {k q qH : ℕ} [NeZero q]
    (φ : WooleyPolynomialSystem k) (γ : WooleySourceSequence)
    (a : Fin k → ZMod q) (ξ : ZMod qH) (n : ℤ)
    (hs : γ.support.filter (fun m : ℤ => (m : ZMod qH) = ξ) = {n}) :
    ‖wooleySourceNormalizedPolynomialResidueSum φ γ a ξ‖ = 1 := by
  have hn : n ∈ γ.support := by
    have : n ∈ γ.support.filter (fun m : ℤ => (m : ZMod qH) = ξ) := by rw [hs]; simp
    exact (Finset.mem_filter.mp this).1
  have hn0 : γ n ≠ 0 := Finsupp.mem_support_iff.mp hn
  have hnorm0 : ‖γ n‖ ≠ 0 := norm_ne_zero_iff.mpr hn0
  have hmass : wooleySourceResidueMassSq γ qH ξ = ‖γ n‖ ^ 2 := by
    simp [wooleySourceResidueMassSq, hs]
  rw [wooleySourceNormalizedPolynomialResidueSum, hmass,
    if_neg (pow_ne_zero _ hnorm0), wooleySourcePolynomialResidueSum, hs,
    Finset.sum_singleton, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_sq (norm_nonneg _), norm_mul, wooleySourcePolynomialPhase_norm,
    mul_one, inv_mul_cancel₀ hnorm0]

/-- The full native conditioned mean is one for a nonzero source whose
support is injective modulo the lower modulus. -/
theorem source_conditioned_mean_of_residue_injective {k : ℕ}
    (s q qH : ℕ) [NeZero q] [NeZero qH]
    (φ : WooleyPolynomialSystem k) (γ : WooleySourceSequence)
    (hmass : wooleySourceMassSq γ ≠ 0)
    (hinj : Set.InjOn (fun n : ℤ => (n : ZMod qH)) γ.support) :
    wooleySourcePolynomialConditionedMean s q qH φ γ = 1 := by
  have hterm (ξ : ZMod qH) :
      wooleySourceResidueMassSq γ qH ξ *
        (((q ^ k : ℕ) : ℝ)⁻¹ * ∑ a : Fin k → ZMod q,
          ‖wooleySourceNormalizedPolynomialResidueSum φ γ a ξ‖ ^ (2 * s)) =
      wooleySourceResidueMassSq γ qH ξ := by
    let S := γ.support.filter (fun n : ℤ => (n : ZMod qH) = ξ)
    have hS : S.card ≤ 1 := Finset.card_le_one.mpr (by
      intro n hn m hm
      obtain ⟨hn, hnξ⟩ := Finset.mem_filter.mp hn
      obtain ⟨hm, hmξ⟩ := Finset.mem_filter.mp hm
      exact hinj hn hm (hnξ.trans hmξ.symm))
    by_cases hne : S.Nonempty
    · obtain ⟨n, hn⟩ := hne
      have hsingle : S = {n} := by
        ext m
        constructor
        · intro hm
          exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hS m hm n hn)
        · intro hm
          simpa only [Finset.mem_singleton.mp hm] using hn
      have hnorm (a : Fin k → ZMod q) :
          ‖wooleySourceNormalizedPolynomialResidueSum φ γ a ξ‖ = 1 :=
        source_singleton_residue_normalized_norm φ γ a ξ n hsingle
      simp only [hnorm, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_fin, ZMod.card, nsmul_eq_mul, mul_one]
      rw [inv_mul_cancel₀ (by exact_mod_cast pow_ne_zero k (NeZero.ne q)), mul_one]
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hzero : wooleySourceResidueMassSq γ qH ξ = 0 := by
        change (∑ n ∈ S, ‖γ n‖ ^ 2) = 0
        simp [hempty]
      simp [hzero]
  unfold wooleySourcePolynomialConditionedMean
  rw [if_neg hmass]
  simp_rw [hterm]
  rw [wooleySource_sum_residueMassSq, inv_mul_cancel₀ hmass]

theorem weightedIntegerSource_real_mass (labels : α ↪ ℤ) (w : α → ℝ) :
    wooleySourceMassSq (weightedIntegerSource labels (fun x => (w x : ℂ))) = ∑ x, w x ^ 2 := by
  rw [weightedIntegerSource_mass]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The literal native global mean equals the weighted congruence energy
divided by the appropriate power of the actual L2 mass. -/
theorem weightedIntegerSource_monomial_mean (q k s : ℕ) [NeZero q]
    (labels : α ↪ ℤ) (w : α → ℝ) (hmass : (∑ x, w x ^ 2) ≠ 0) :
    wooleySourcePolynomialMean s q (wooleyMonomialPolynomialSystem k)
      (weightedIntegerSource labels (fun x => (w x : ℂ))) =
      weightedVinogradovEnergy k s (fun x => (labels x : ZMod q)) w /
        (∑ x, w x ^ 2) ^ s := by
  let γ := weightedIntegerSource labels (fun x => (w x : ℂ))
  have hγ : wooleySourceMassSq γ ≠ 0 := by
    simpa only [γ, weightedIntegerSource_real_mass] using hmass
  have hsum (a : Fin k → ZMod q) :
      wooleySourcePolynomialSum (wooleyMonomialPolynomialSystem k) γ a =
        ∑ x, (w x : ℂ) * ZMod.stdAddChar
          (∑ j : Fin k, a j * (labels x : ZMod q) ^ (j.val + 1)) := by
    rw [wooleySourcePolynomialSum,
      weightedIntegerSource_sum labels (fun x => (w x : ℂ))
        (fun n z => z * wooleySourcePolynomialPhase (wooleyMonomialPolynomialSystem k) a n)
        (by simp)]
    simp only [wooleySourcePolynomialPhase, wooleyMonomialPolynomialSystem,
      Polynomial.eval_pow, Polynomial.eval_X, Int.cast_pow]
  change wooleySourcePolynomialMean s q (wooleyMonomialPolynomialSystem k) γ = _
  unfold wooleySourcePolynomialMean
  simp_rw [norm_wooleySourceNormalizedPolynomialSum_pow_even _ γ _ s hγ, hsum]
  rw [← Finset.mul_sum]
  calc
    _ = (wooleySourceMassSq γ)⁻¹ ^ s *
      (((q ^ k : ℕ) : ℝ)⁻¹ * ∑ a : Fin k → ZMod q,
        ‖∑ x, (w x : ℂ) * ZMod.stdAddChar
          (∑ j : Fin k, a j * (labels x : ZMod q) ^ (j.val + 1))‖ ^ (2 * s)) := by ring
    _ = _ := by
      rw [real_weighted_monomial_grid_mean, weightedIntegerSource_real_mass, inv_pow]
      ring

/-- The native critical theorem with the full L2 mass rather than a support
cardinality factor.  Constants are uniform in all nonnegative bounded
coefficient families and all integer labels. -/
theorem native_monomial_modular_energy_bound_of_bounded (k p : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (H : ℕ) {α : Type*} [Fintype α] (labels : α → ℤ), B0 ≤ k * H →
        Function.Injective (fun x => (labels x : ZMod (p ^ H))) →
        ∀ w : α → ℝ, (∀ x, 0 ≤ w x) → (∀ x, w x ≤ 1) →
        weightedVinogradovEnergy k (wooleyTriangular k)
          (fun x => (labels x : ZMod (p ^ (k * H)))) w ≤
          C * (p ^ (k * H) : ℝ) ^ δ * (∑ x, w x ^ 2) ^ (wooleyTriangular k) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨C, hC, B0, hmain⟩ := wooleyPolynomialCorollary32_native
    k p hp hk hkp 1 δ (by norm_num) hδ
  refine ⟨C, hC, B0, ?_⟩
  intro H α inst labels hB hinj w hw0 hw1
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
    simp [weightedVinogradovEnergy, hwzero, Nat.ne_of_gt hs]
  · let e : α ↪ ℤ := ⟨labels, fun x y h => hinj (congrArg (fun n : ℤ => (n : ZMod (p ^ H))) h)⟩
    let γ := weightedIntegerSource e (fun x => (w x : ℂ))
    have hγ : wooleySourceMassSq γ ≠ 0 := by
      simpa only [γ, weightedIntegerSource_real_mass] using hM
    have hadm : γ.Admissible := weightedIntegerSource_admissible e _ (by
      intro x
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x)] using hw1 x)
    have hres : Set.InjOn (fun n : ℤ => (n : ZMod (p ^ H))) γ.support :=
      weightedIntegerSource_residue_injective e _ _ hinj
    have hPhi : (wooleyMonomialPolynomialSystem k).InPhiTau p (k * H) 1 := by
      refine ⟨k * H, wooleyMonomialPolynomialSystem_spaced k p (k * H), ?_⟩
      norm_num
    have hbound := hmain (k * H) (wooleyMonomialPolynomialSystem k) γ hB hPhi hadm
    simp only [wooley_mul_ceilDiv_self hk] at hbound
    rw [source_conditioned_mean_of_residue_injective _ _ _ _ γ hγ hres,
      weightedIntegerSource_monomial_mean _ _ _ e w hM, mul_one] at hbound
    exact (div_le_iff₀ (pow_pos (lt_of_le_of_ne hM0 (Ne.symm hM)) _)).mp hbound

/-- Homogeneity removes the coefficient bound in the native source class.
This is the full nonnegative weighted congruence-energy estimate. -/
theorem native_monomial_modular_energy_bound (k p : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) (hkp : k < p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (H : ℕ) {α : Type*} [Fintype α] (labels : α → ℤ), B0 ≤ k * H →
        Function.Injective (fun x => (labels x : ZMod (p ^ H))) →
        ∀ w : α → ℝ, (∀ x, 0 ≤ w x) →
        weightedVinogradovEnergy k (wooleyTriangular k)
          (fun x => (labels x : ZMod (p ^ (k * H)))) w ≤
          C * (p ^ (k * H) : ℝ) ^ δ * (∑ x, w x ^ 2) ^ (wooleyTriangular k) := by
  obtain ⟨C, hC, B0, hmain⟩ := native_monomial_modular_energy_bound_of_bounded k p hp hk hkp hδ
  refine ⟨C, hC, B0, ?_⟩
  intro H α inst labels hB hinj w hw
  let M : ℝ := 1 + ∑ x, w x
  have hM : 0 < M := by
    have hsum : 0 ≤ ∑ x, w x := Finset.sum_nonneg (fun x _ => hw x)
    dsimp [M]
    linarith
  have hwM (x : α) : w x ≤ M := by
    have h := Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ x)
    dsimp [M]
    linarith
  have hb := hmain H labels hB hinj (fun x => M⁻¹ * w x)
    (fun x => mul_nonneg (inv_nonneg.mpr hM.le) (hw x))
    (fun x => by
      calc
        M⁻¹ * w x ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hwM x) (inv_nonneg.mpr hM.le)
        _ = 1 := inv_mul_cancel₀ hM.ne')
  rw [weightedVinogradovEnergy_mul] at hb
  have hmass : (∑ x, (M⁻¹ * w x) ^ 2) ^ (wooleyTriangular k) =
      M⁻¹ ^ (2 * wooleyTriangular k) * (∑ x, w x ^ 2) ^ (wooleyTriangular k) := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, mul_pow, ← pow_mul]
  rw [hmass] at hb
  have hpos : 0 < M⁻¹ ^ (2 * wooleyTriangular k) := by positivity
  apply (mul_le_mul_left hpos).mp
  calc
    _ ≤ _ := hb
    _ = _ := by ring

#print axioms source_conditioned_mean_of_residue_injective
#print axioms native_monomial_modular_energy_bound

end WaringSiegel.WSL3
