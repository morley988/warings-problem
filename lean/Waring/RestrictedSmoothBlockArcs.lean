import Waring.RestrictedSmoothMixedArcs

/-! # Scaling and summing all literal coprime blocks on rational arcs -/

noncomputable section
open scoped BigOperators
namespace Waring.RestrictedSmoothArcs
open SmoothMoments RestrictedSmoothFactorization

theorem scaled_mixedPrimeWeyl_arcs_epsilon (k : ℕ) {s : ℕ} (hs : 1 ≤ s)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P → ∀ S : Finset ℕ+,∀ Q δ : ℝ,
      1 ≤ Q → 0 ≤ δ → (∀ q ∈ S,(q : ℝ) ≤ Q) →
      (∀ q ∈ S,(q : ℝ) ≤ P^B) → ∀ m : ℕ,0 < m →
      4*Q*((m : ℝ)^k*δ) ≤ 1 → ∀ X R : ℝ,0 ≤ X → X ≤ P →
      ∀ π : ℕ,(π : ℝ) ≤ R →
      (∑ q ∈ S.filter (fun q : ℕ+ => m.Coprime (q : ℕ)),
        rationalArcSum (q : ℕ) (fun x => ‖mixedPrimeWeyl k q π X R ((m : ℝ)^k*x)‖^s) δ) ≤
      C*P^ε*((m : ℝ)^k)⁻¹*∑ z ∈ smoothNumbers X R,smoothMoment k s (X/(z : ℝ)) π := by
  obtain ⟨C,hC,hbound⟩ := mixedPrimeWeyl_arcs_epsilon k hs hB hε
  refine ⟨C,hC,?_⟩
  intro P hP S Q δ hQ1 hδ hQ hqP m hm hsep X R hX hXP π hπR
  have hδm : 0 ≤ (m : ℝ)^k*δ := by positivity
  have hδm1 : (m : ℝ)^k*δ ≤ 1 := by
    have hfour : 1 ≤ 4*Q := by linarith
    exact (le_mul_of_one_le_left hδm hfour).trans hsep
  have hper (q : ℕ+) : Function.Periodic (fun x => ‖mixedPrimeWeyl k q π X R x‖^s) 1 :=
    fun x => by dsimp only; rw [periodic_mixedPrimeWeyl k q π X R x]
  have heq (q : ℕ+) (hq : q ∈ S.filter (fun q : ℕ+ => m.Coprime (q : ℕ))) :
      rationalArcSum (q : ℕ) (fun x => ‖mixedPrimeWeyl k q π X R ((m : ℝ)^k*x)‖^s) δ =
        ((m : ℝ)^k)⁻¹*rationalArcSum (q : ℕ) (fun x => ‖mixedPrimeWeyl k q π X R x‖^s)
          ((m : ℝ)^k*δ) := by
    simpa only [Nat.cast_pow] using rationalArcSum_mul_nat (q : ℕ) (hper q)
      (m^k) (pow_pos hm k) ((Finset.mem_filter.mp hq).2.pow_left k) δ
  calc
    _ = ((m : ℝ)^k)⁻¹*∑ q ∈ S.filter (fun q : ℕ+ => m.Coprime (q : ℕ)),
        rationalArcSum (q : ℕ) (fun x => ‖mixedPrimeWeyl k q π X R x‖^s) ((m : ℝ)^k*δ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl heq
    _ ≤ ((m : ℝ)^k)⁻¹*(C*P^ε*∑ z ∈ smoothNumbers X R,smoothMoment k s (X/(z : ℝ)) π) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hbound P hP _ Q _ hδm hδm1 hsep
        (fun q hq => hQ q (Finset.mem_filter.mp hq).1)
        (fun q hq => hqP q (Finset.mem_filter.mp hq).1) X R hX hXP π hπR
    _ = _ := by ring

def blockArcTotal (k s : ℕ) (S : Finset ℕ+) (P R M δ : ℝ) : ℝ :=
  ∑ q ∈ S,∑ b ∈ coprimeBlocks q M R,
    rationalArcSum (q : ℕ) (fun x =>
      ‖mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R ((b.2 : ℝ)^k*x)‖^s) δ

theorem blockArcTotal_comm (k s : ℕ) (S : Finset ℕ+) (P R M δ : ℝ) :
    blockArcTotal k s S P R M δ = ∑ b ∈ orderedBlocks M R,
      ∑ q ∈ S.filter (fun q : ℕ+ => b.2.Coprime (q : ℕ)),
        rationalArcSum (q : ℕ) (fun x =>
          ‖mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R ((b.2 : ℝ)^k*x)‖^s) δ := by
  classical
  unfold blockArcTotal coprimeBlocks
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]

theorem orderedBlocks_bounds {M R : ℝ} (hM : 1 ≤ M) (hR : 1 ≤ R)
    {b : ℕ × ℕ} (hb : b ∈ orderedBlocks M R) :
    0 < b.2 ∧ M < (b.2 : ℝ) ∧ (b.2 : ℝ) ≤ M*R ∧ (b.1 : ℝ) ≤ R := by
  classical
  rcases Finset.mem_filter.mp hb with ⟨hb,hprime,hdiv,hlo,hhi,hrough⟩
  rcases Finset.mem_product.mp hb with ⟨hπ,hm⟩
  have hm' := mem_smoothNumbers.mp hm
  have hπR : (b.1 : ℝ) ≤ R := (Nat.cast_le.mpr (Finset.mem_Icc.mp hπ).2).trans
    (Nat.floor_le (zero_le_one.trans hR))
  exact ⟨hm'.1.1,hlo,hhi.trans (mul_le_mul_of_nonneg_left hπR (zero_le_one.trans hM)),hπR⟩

theorem blockArcTotal_epsilon (k : ℕ) {s : ℕ} (hs : 1 ≤ s)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P → ∀ S : Finset ℕ+,∀ Q δ R M : ℝ,
      1 ≤ Q → 0 ≤ δ → 1 ≤ R → 1 ≤ M → M*R ≤ P →
      (∀ q ∈ S,(q : ℝ) ≤ Q) → (∀ q ∈ S,(q : ℝ) ≤ P^B) →
      (∀ b ∈ orderedBlocks M R,4*Q*((b.2 : ℝ)^k*δ) ≤ 1) →
      blockArcTotal k s S P R M δ ≤ C*P^ε*
        ∑ b ∈ orderedBlocks M R,((b.2 : ℝ)^k)⁻¹*
          ∑ z ∈ smoothNumbers (P/(b.2 : ℝ)) R,smoothMoment k s ((P/(b.2 : ℝ))/(z : ℝ)) b.1 := by
  obtain ⟨C,hC,hbound⟩ := scaled_mixedPrimeWeyl_arcs_epsilon k hs hB hε
  refine ⟨C,hC,?_⟩
  intro P hP S Q δ R M hQ1 hδ hR hM hMR hQ hqP hsep
  rw [blockArcTotal_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  obtain ⟨hm,hMm,hmMR,hπ⟩ := orderedBlocks_bounds hM hR hb
  have hm1 : (1 : ℝ) ≤ b.2 := by exact_mod_cast hm
  have hX : 0 ≤ P/(b.2 : ℝ) := div_nonneg (zero_le_one.trans hP) (Nat.cast_nonneg _)
  have hXP : P/(b.2 : ℝ) ≤ P := div_le_self (zero_le_one.trans hP) hm1
  simpa only [mul_assoc] using hbound P hP S Q δ hQ1 hδ hQ hqP b.2 hm (hsep b hb)
    (P/(b.2 : ℝ)) R hX hXP b.1 hπ

#print axioms blockArcTotal_epsilon
end Waring.RestrictedSmoothArcs
