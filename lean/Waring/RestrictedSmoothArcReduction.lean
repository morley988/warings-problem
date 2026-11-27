import Waring.RestrictedSmoothBlockArcs

/-! # The actual smooth arc mean reduced to complete shorter moments -/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Waring.RestrictedSmoothArcs
open SmoothMoments RestrictedSmoothFactorization

theorem rationalArcSum_add (q : ℕ) [NeZero q] (δ : ℝ) {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G) :
    rationalArcSum q (fun x => F x+G x) δ=rationalArcSum q F δ+rationalArcSum q G δ := by
  unfold rationalArcSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact intervalIntegral.integral_add
    ((hF.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
    ((hG.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)

theorem continuous_smallCoprimeSum (k q : ℕ) (P R M : ℝ) :
    Continuous (smallCoprimeSum k q P R M) :=
  continuous_finset_sum _ (fun p _ => continuous_phase k (p.1*p.2))

theorem smooth_arc_block_reduction (k q : ℕ) [NeZero q] {s : ℕ} (hs : 1 ≤ s)
    {P R M δ : ℝ} (hP : 0 ≤ P) (hR : 1 ≤ R) (hM : 1 ≤ M) (hδ : 0 ≤ δ) :
    rationalArcSum q (fun x => ‖smoothWeyl k P R x‖^s) δ ≤
      (2 : ℝ)^(s-1)*(rationalArcSum q (fun x => ‖smallCoprimeSum k q P R M x‖^s) δ+
        (M*R)^(s-1)*∑ b ∈ coprimeBlocks q M R,rationalArcSum q
          (fun x => ‖mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R ((b.2 : ℝ)^k*x)‖^s) δ) := by
  have hMR : 0 ≤ M*R := by positivity
  have hsmall := (continuous_smallCoprimeSum k q P R M).norm.pow s
  have hblock (b : ℕ × ℕ) : Continuous (fun x : ℝ =>
      ‖mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R ((b.2 : ℝ)^k*x)‖^s) :=
    ((continuous_mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R).comp
      (continuous_const.mul continuous_id)).norm.pow s
  have hsum := continuous_finset_sum (coprimeBlocks q M R) (fun b _ => hblock b)
  calc
    _ ≤ rationalArcSum q (fun x => (2 : ℝ)^(s-1)*
        (‖smallCoprimeSum k q P R M x‖^s+(M*R)^(s-1)*
          ∑ b ∈ coprimeBlocks q M R,
            ‖mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R ((b.2 : ℝ)^k*x)‖^s)) δ :=
      rationalArcSum_mono q hδ ((continuous_smoothWeyl k P R).norm.pow s)
        (continuous_const.mul (hsmall.add (continuous_const.mul hsum)))
        (fun x => smoothWeyl_coprime_block_bound k q hs hP hM hMR)
    _ = _ := by
      rw [rationalArcSum_const_mul,rationalArcSum_add q δ hsmall (continuous_const.mul hsum),
        rationalArcSum_const_mul,rationalArcSum_finset_sum _ q _ δ (fun b _ => hblock b)]

def blockMomentSum (k s : ℕ) (P R M : ℝ) : ℝ :=
  ∑ b ∈ orderedBlocks M R,((b.2 : ℝ)^k)⁻¹*
    ∑ z ∈ smoothNumbers (P/(b.2 : ℝ)) R,smoothMoment k s ((P/(b.2 : ℝ))/(z : ℝ)) b.1

theorem blockMomentSum_nonneg (k s : ℕ) (P R M : ℝ) : 0 ≤ blockMomentSum k s P R M := by
  unfold blockMomentSum
  apply Finset.sum_nonneg
  intro b hb
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun z _ => smoothMoment_nonneg ..))

theorem smooth_arcs_reduction_epsilon (k : ℕ) {s : ℕ} (hs : 1 ≤ s)
    {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ P : ℝ,1 ≤ P → ∀ S : Finset ℕ+,∀ Q δ R M : ℝ,
      1 ≤ Q → 0 ≤ δ → 1 ≤ R → 1 ≤ M → M*R ≤ P →
      (∀ q ∈ S,(q : ℝ) ≤ Q) → (∀ q ∈ S,(q : ℝ) ≤ P^B) →
      (∀ b ∈ orderedBlocks M R,4*Q*((b.2 : ℝ)^k*δ) ≤ 1) →
      (∑ q ∈ S,rationalArcSum (q : ℕ) (fun x => ‖smoothWeyl k P R x‖^s) δ) ≤
        C*P^ε*(Q*δ*M^s+(M*R)^(s-1)*blockMomentSum k s P R M) := by
  obtain ⟨A,hA,hsmall⟩ := smallCoprimeSum_power_bound s hB hε
  obtain ⟨D,hD,hlarge⟩ := blockArcTotal_epsilon k hs hB hε
  refine ⟨(2 : ℝ)^(s-1)*(2*A+D),by positivity,?_⟩
  intro P hP S Q δ R M hQ1 hδ hR hM hMR hQ hqP hsep
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hsbound : (∑ q ∈ S,rationalArcSum (q : ℕ)
      (fun x => ‖smallCoprimeSum k q P R M x‖^s) δ) ≤ 2*Q*δ*(A*P^ε*M^s) := by
    apply le_trans (Finset.sum_le_sum (fun (q : ℕ+) hq => rationalArcSum_mono q hδ
      ((continuous_smallCoprimeSum k q P R M).norm.pow s) continuous_const
      (fun x => hsmall P hP q q.pos (hqP q hq) R M x hM0 k)))
    exact sum_constant_arc_integrals_le S (zero_le_one.trans hQ1) hQ hδ (by positivity)
  have hlbound : blockArcTotal k s S P R M δ ≤ D*P^ε*blockMomentSum k s P R M := by
    simpa only [blockMomentSum] using
      hlarge P hP S Q δ R M hQ1 hδ hR hM hMR hQ hqP hsep
  have hX0 : 0 ≤ Q*δ*M^s := by positivity
  have hY0 : 0 ≤ (M*R)^(s-1)*blockMomentSum k s P R M :=
    mul_nonneg (by positivity) (blockMomentSum_nonneg ..)
  have hcoeff : 2*A*(Q*δ*M^s)+D*((M*R)^(s-1)*blockMomentSum k s P R M) ≤
      (2*A+D)*(Q*δ*M^s+(M*R)^(s-1)*blockMomentSum k s P R M) := by
    nlinarith [mul_nonneg hD.le hX0,mul_nonneg hA.le hY0]
  calc
    _ ≤ ∑ q ∈ S,(2 : ℝ)^(s-1)*
        (rationalArcSum (q : ℕ) (fun x => ‖smallCoprimeSum k q P R M x‖^s) δ+
        (M*R)^(s-1)*∑ b ∈ coprimeBlocks q M R,rationalArcSum (q : ℕ)
          (fun x => ‖mixedPrimeWeyl k q b.1 (P/(b.2 : ℝ)) R ((b.2 : ℝ)^k*x)‖^s) δ) :=
      Finset.sum_le_sum (fun q _ => smooth_arc_block_reduction k q hs hP0 hR hM hδ)
    _ = (2 : ℝ)^(s-1)*((∑ q ∈ S,rationalArcSum (q : ℕ)
        (fun x => ‖smallCoprimeSum k q P R M x‖^s) δ)+(M*R)^(s-1)*blockArcTotal k s S P R M δ) := by
      simp only [blockArcTotal,Finset.mul_sum,Finset.sum_add_distrib,mul_add]
    _ ≤ (2 : ℝ)^(s-1)*(2*Q*δ*(A*P^ε*M^s)+(M*R)^(s-1)*(D*P^ε*blockMomentSum k s P R M)) := by
      gcongr
    _ = (2 : ℝ)^(s-1)*P^ε*(2*A*(Q*δ*M^s)+D*((M*R)^(s-1)*blockMomentSum k s P R M)) := by ring
    _ ≤ (2 : ℝ)^(s-1)*P^ε*((2*A+D)*(Q*δ*M^s+(M*R)^(s-1)*blockMomentSum k s P R M)) :=
      mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ = _ := by ring

#print axioms smooth_arcs_reduction_epsilon
end Waring.RestrictedSmoothArcs
