import Waring.PolicyCompletionEvenLowDegreeSource
import Waring.SeedCompletionTerminalOddSecond

/-! # A common sharp second moment for odd residuals and degrees two and four -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionSharpResidualSource
open PolicyCompletionEvenLowDegreeSource SeedCompletionTerminalOddSecond
open SeedCompletionTerminalPhase SeedCompletionTerminalSecond SeedCompletionTerminalCurves
open SeedCompletionSparseWeighted

def SharpResidual (k j : ℕ) : Prop:=Odd (k+j) ∨ k-j=2 ∨ k-j=4

theorem sharp_source_second_moment {k j : ℕ} (hj : j<k) (hgood : SharpResidual k j)
    {L ε : ℝ} (hL : 0≤L) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→∀H B : Finset (Fin j→ℕ),
      (∀h∈H,∀i,0<h i)→(∀m∈B,∀i,0<m i)→
      ∀Z : Finset ℕ,(∀z∈Z,0<z)→
      (∀h∈H,∀m∈B,∀z∈Z,((phase k h m z).natAbs:ℝ)≤P^L)→
      (∀h∈H,∀m∈B,(phase k h m 1:ℝ)≤P^L)→
      sourceSecondMoment k H B Z≤
        C*P^ε*((Z.card:ℝ)*(∑h∈H,((samePolynomialPairs B (realPolynomial k h)).card:ℝ))+
          (H.card:ℝ)*(B.card:ℝ)^2) := by
  rcases hgood with hodd|hlow
  · obtain ⟨C,hC,hbound⟩:=odd_source_second_moment hj hodd hL hε
    have hd : (1:ℝ)≤(k-j:ℕ):=by exact_mod_cast (show 1≤k-j by omega)
    refine ⟨C*((k-j:ℕ):ℝ),by positivity,?_⟩
    intro P hP H B hH hB Z hZ hsize hone
    apply (hbound P hP H B hH hB Z hZ hsize).trans
    calc
      _ ≤ C*P^ε*(((k-j:ℕ):ℝ)*((Z.card:ℝ)*
          (∑h∈H,((samePolynomialPairs B (realPolynomial k h)).card:ℝ)))+
          ((k-j:ℕ):ℝ)*(H.card:ℝ)*(B.card:ℝ)^2):=by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add_right
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hd
          (by positivity : 0≤(Z.card:ℝ)*(∑h∈H,((samePolynomialPairs B (realPolynomial k h)).card:ℝ)))
      _ = _:=by ring
  · exact low_source_second_moment hj hlow hL hε

theorem sharp_source_second_to_weighted {k j J : ℕ} (hj : j<k)
    (hgood : SharpResidual k j) (hrec : SparseRecognition k j J)
    {L ε : ℝ} (hL : 0≤L) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→∀H A : Fin j→Finset ℕ,
      (∀i,∀h∈H i,0<h)→(∀i,∀m∈A i,0<m)→
      ∀Z : Finset ℕ,(∀z∈Z,0<z)→
      (∀h∈Fintype.piFinset H,∀m∈Fintype.piFinset A,∀z∈Z,((phase k h m z).natAbs:ℝ)≤P^L)→
      (∀h∈Fintype.piFinset H,∀m∈Fintype.piFinset A,(phase k h m 1:ℝ)≤P^L)→
      sourceSecondMoment k (Fintype.piFinset H) (Fintype.piFinset A) Z≤
        C*P^ε*((Z.card:ℝ)*(weightedCount H A
          (fun _=>progressionPhase (J:=J) (2*k) 2):ℝ)+
          ((Fintype.piFinset H).card:ℝ)*((Fintype.piFinset A).card:ℝ)^2) := by
  obtain ⟨C,hC,hbound⟩:=sharp_source_second_moment hj hgood hL hε
  refine ⟨C,hC,?_⟩
  intro P hP H A hH hA Z hZ hsize hone
  have hhpos (h) (hh : h∈Fintype.piFinset H) (i) : 0<h i:=
    hH i _ (Fintype.mem_piFinset.mp hh i)
  apply (hbound P hP (Fintype.piFinset H) (Fintype.piFinset A) hhpos
    (fun m hm i=>hA i _ (Fintype.mem_piFinset.mp hm i)) Z hZ hsize hone).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Z.card)
  simp only [weightedCount,Nat.cast_sum]
  exact Finset.sum_le_sum (fun h hh=>by
    exact_mod_cast samePolynomialPairs_le_vector hrec h (hhpos h hh) A hA)

#print axioms sharp_source_second_moment
#print axioms sharp_source_second_to_weighted
end Waring.PolicyCompletionSharpResidualSource
