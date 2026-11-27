import WaringSiegel.WSL3CubicKappaIdeal

/-! # WSL3: actual finite ideal sums for the cubic conductor weight -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem cubicKappa_finite_weighted_sum_le
    (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hC : ∀ v, 0 ≤ C v)
    (m : ℕ) (t a : ℝ) (hta : t ≤ a)
    (hs : Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      (Ideal.absNorm I.1 : ℝ)^t*cubicKappa C I^m))
    (L : ℝ) (hL : 1 ≤ L) (S : Finset {I : Ideal (𝓞 K) // I ≠ 0})
    (hS : ∀ I ∈ S, (Ideal.absNorm I.1 : ℝ) ≤ L) :
    (∑ I ∈ S, (Ideal.absNorm I.1 : ℝ)^a*cubicKappa C I^m) ≤
      (∑' I : {I : Ideal (𝓞 K) // I ≠ 0},
        (Ideal.absNorm I.1 : ℝ)^t*cubicKappa C I^m)*L^(a-t) := by
  have hf (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
      0 ≤ (Ideal.absNorm I.1 : ℝ)^t*cubicKappa C I^m :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (cubicKappa_nonneg C hC I) _)
  calc
    _ ≤ ∑ I ∈ S, ((Ideal.absNorm I.1 : ℝ)^t*cubicKappa C I^m)*L^(a-t) := by
      apply Finset.sum_le_sum
      intro I hI
      have hN : 0 < (Ideal.absNorm I.1 : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp I.2)
      have he : (Ideal.absNorm I.1 : ℝ)^a*cubicKappa C I^m =
          ((Ideal.absNorm I.1 : ℝ)^t*cubicKappa C I^m)*(Ideal.absNorm I.1 : ℝ)^(a-t) := by
        calc
          _ = (Ideal.absNorm I.1 : ℝ)^(t+(a-t))*cubicKappa C I^m := by congr 2 <;> ring
          _ = _ := by rw [Real.rpow_add hN]; ring
      rw [he]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hN.le (hS I hI) (sub_nonneg.mpr hta)) (hf I)
    _ = (∑ I ∈ S, (Ideal.absNorm I.1 : ℝ)^t*cubicKappa C I^m)*L^(a-t) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (hs.sum_le_tsum S (fun I _ => hf I)) (Real.rpow_nonneg (by linarith) _)

/-- A single constant gives both manuscript fourth-power truncation
estimates: set a=1, or a=4/3. The finite family is arbitrary under its actual
ideal-norm cutoff, so the result applies directly to conductor sums. -/
theorem cubicKappa_fourth_truncation_bound
    (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hC : ∀ v, 0 ≤ C v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ (a : ℝ), 1-ε ≤ a →
      ∀ (L : ℝ), 1 ≤ L → ∀ (S : Finset {I : Ideal (𝓞 K) // I ≠ 0}),
      (∀ I ∈ S, (Ideal.absNorm I.1 : ℝ) ≤ L) →
      (∑ I ∈ S, (Ideal.absNorm I.1 : ℝ)^a*cubicKappa C I^4) ≤ B*L^(a-1+ε) := by
  let B := ∑' I : {I : Ideal (𝓞 K) // I ≠ 0},
    (Ideal.absNorm I.1 : ℝ)^(1-ε)*cubicKappa C I^4
  have hB : 0 ≤ B := tsum_nonneg (fun I => by positivity)
  refine ⟨B+1,by linarith,?_⟩
  intro a ha L hL S hS
  have hb := cubicKappa_finite_weighted_sum_le C hC 4 (1-ε) a ha
    (cubicKappa_fourth_weighted_summable C hC (1-ε) (by linarith)) L hL S hS
  change _ ≤ B*L^(a-(1-ε)) at hb
  rw [show a-(1-ε)=a-1+ε by ring] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _))

theorem cubicKappa_fourth_norm_truncation_bound
    (C : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ) (hC : ∀ v, 0 ≤ C v)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (S : Finset {I : Ideal (𝓞 K) // I ≠ 0}),
      (∀ I ∈ S, (Ideal.absNorm I.1 : ℝ) ≤ L) →
      (∑ I ∈ S, (Ideal.absNorm I.1 : ℝ)*cubicKappa C I^4) ≤ B*L^ε := by
  obtain ⟨B,hB,hbound⟩ := cubicKappa_fourth_truncation_bound C hC ε hε
  refine ⟨B,hB,?_⟩
  intro L hL S hS
  simpa only [Real.rpow_one,sub_self,zero_add] using hbound 1 (by linarith) L hL S hS

end WaringSiegel
#print axioms WaringSiegel.cubicKappa_fourth_truncation_bound
#print axioms WaringSiegel.cubicKappa_fourth_norm_truncation_bound
