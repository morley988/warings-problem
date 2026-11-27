import Waring.SeedCompletionFundamentalScale
import Waring.PolicyCompletionPositivePhase

/-!
# The actual source recurrence on bounded positive parameter boxes

All polynomial premises of the absorbed fundamental estimate are proved
here for the recursively defined centered-power phase. Positivity removes
the zero-derivative branch and gives the initial center injection; the
already proved integer-polynomial size estimate supplies its uniform
ambient power. Only finite domains and their displayed size bounds remain.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSourceCount
open SmoothMoments IntegerDifferencePolynomial PolicyCompletionPositivePhase
open PolicyCompletionFundamental PolicyCompletionGoodBranch SeedCompletionSharpBackward
open SeedCompletionFundamentalScale SeedCompletionAbsorbedFundamental

theorem source_recurrence_count {κ : Type*} [DecidableEq κ] (k s : ℕ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∃ P₀ : ℝ, 1 ≤ P₀ ∧ ∀ P : ℝ, P₀ ≤ P →
      ∀ (C : Finset κ) (params : κ → List (ℤ × ℤ)),
      (∀ c ∈ C, ∀ hm ∈ params c, 0 < hm.1 ∧ 0 < hm.2) →
      (∀ c ∈ C, (params c).length < k) →
      (∀ c ∈ C, ∀ hm ∈ params c, (hm.1 : ℝ) ≤ P ∧ (hm.2 : ℝ) ≤ P) →
      ∀ (N : ℤ), (N : ℝ) ≤ P → ∀ (Z : Finset ℤ), Z ⊆ Finset.Icc 1 N →
      ∀ Q R M : ℝ, 1 ≤ M → M ≤ Q → Q ≤ P → P^η ≤ R →
      sourceMixedMoment k (s+1) C params Z Q R ≤
        K*P^ε*((C.card : ℝ)^2*(Z.card : ℝ)*(M*R)^(2*(s+1))*
          smoothMoment k (2*(s+1)) (Q/M) R+
          (C.card : ℝ)*(M*R)^(2*(s+1)-1)*
            commonTotal k (s+1) C Z (fun c => powerPolynomial k (params c)) Q R M) := by
  let B : ℝ := (((k+1)*(k-1)+1 : ℕ) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨K,hK,hrec⟩ := fundamental_absorbed_scale (κ := κ) k s hB hη hε
  obtain ⟨P₀,hP₀,hsize⟩ := derivative_magnitude_polynomial_bound k k
  refine ⟨K,hK,P₀,hP₀,?_⟩
  intro P hPP C params hpos hlen hbox N hNP Z hZ Q R M hM hMQ hQP hR
  have hm : ∀ c ∈ C, ∀ p ∈ params c, p.2 ≠ 0 :=
    fun c hc p hp => (hpos c hc p hp).2.ne'
  have hinj : ∀ c ∈ C, Set.InjOn (powerPolynomial k (params c)).eval Z := by
    intro c hc
    apply (powerPolynomial_eval_injOn k (params c) (hpos c hc) (hlen c hc)).mono
    intro z hz
    exact (show (0 : ℤ) ≤ 1 by norm_num).trans (Finset.mem_Icc.mp (hZ hz)).1
  have hdeg : ∀ c ∈ C, (powerPolynomial k (params c)).natDegree ≤ k := by
    intro c hc
    exact (powerPolynomial_natDegree_le k (params c) (hm c hc)).trans (Nat.sub_le _ _)
  apply hrec C Z (fun c => powerPolynomial k (params c)) hdeg hinj P Q R M hM hMQ hQP hR
  intro a ha
  obtain ⟨hc,hz⟩ := Finset.mem_product.mp ha
  have hzlo : (0 : ℤ) < a.2 := lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp (hZ hz)).1
  have hzP : |(a.2 : ℝ)| ≤ P := by
    rw [abs_of_pos (by exact_mod_cast hzlo)]
    exact (by exact_mod_cast (Finset.mem_Icc.mp (hZ hz)).2 : (a.2 : ℝ) ≤ N).trans hNP
  have hpar : ∀ p ∈ params a.1, |(p.1 : ℝ)| ≤ P ∧ |(p.2 : ℝ)| ≤ P := by
    intro p hp
    rw [abs_of_pos (by exact_mod_cast (hpos a.1 hc p hp).1),
      abs_of_pos (by exact_mod_cast (hpos a.1 hc p hp).2)]
    exact hbox a.1 hc p hp
  refine ⟨?_,hsize P hPP (params a.1) (hlen a.1 hc).le (hm a.1 hc) hpar a.2 hzP⟩
  change ((powerPolynomial k (params a.1)).derivative.eval a.2).natAbs ≠ 0
  exact Int.natAbs_ne_zero.mpr (powerPolynomial_derivative_eval_pos k (params a.1)
    (hpos a.1 hc) (hlen a.1 hc) hzlo).ne'

#print axioms source_recurrence_count
end Waring.SeedCompletionSourceCount
