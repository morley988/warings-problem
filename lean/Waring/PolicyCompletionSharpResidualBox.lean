import Waring.PolicyCompletionSharpResidualPadded

/-! # Sharp boxed source energy under the sparse diagonal condition -/
noncomputable section
open scoped BigOperators
namespace Waring.PolicyCompletionSharpResidualBox
open SeedCompletionTerminalSparse SeedCompletionSparseWeighted
open PolicyCompletionSharpResidualPadded PolicyCompletionSharpResidualSource

theorem sharp_padded_second_moment_box {k j r : ℕ} (hk : k≤18)
    (hjk : j+r<k) (hj : 1≤j) (hgood : SharpResidual k (j+r))
    (hJ : 2≤(k-(j+r))/2) (hjJ : j≤(k-(j+r))/2+1)
    {B ε : ℝ} (hB : 1≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∃P₀ : ℝ,1≤P₀ ∧ ∀P : ℝ,P₀≤P→
      ∀(H A : Fin j→Finset ℕ) (G : Fin r→Finset ℕ)
        (Hcap M : Fin j→ℝ) (Gcap : Fin r→ℝ),
      (∀i,0<Hcap i)→(∀i,(H i).card≤Hcap i)→
      (∀i,0<Gcap i)→(∀i,(G i).card≤Gcap i)→
      (∀i,∀h∈H i,0<h ∧ (h:ℝ)≤P^B)→
      (∀i,∀h∈G i,0<h ∧ (h:ℝ)≤P^B)→
      (∀i,∀m∈A i,0<m ∧ (m:ℝ)≤M i)→
      (∀i,1≤M i)→(∀i,M i≤P^B)→(∀i,(A i).card≤M i)→
      ∀Z : Finset ℕ,(∀z∈Z,0<z ∧ (z:ℝ)≤P)→(Z.card:ℝ)≤P→
      paddedSecondMoment k H A G Z≤
        C*P^ε*((P+(∏i,M i))*((∏i,Hcap i)*(∏i,Gcap i)*(∏i,M i))) := by
  obtain ⟨C₀,hC₀,P₀,hP₀,hsource⟩:=sharp_padded_second_moment_to_weighted hk hjk hj hgood hB
    (show 0<ε/2 by positivity)
  obtain ⟨C₁,hC₁,hweight⟩:=weighted_even_progression_subpower k ((k-(j+r))/2) j
    (by omega) hJ hj hjJ (zero_le_one.trans hB) (show 0<ε/2 by positivity)
  refine ⟨C₀*(C₁+1),by positivity,P₀,hP₀,?_⟩
  intro P hPP H A G Hcap M Gcap hHpos hHcard hGpos hGcard hH hG hA hM hMP hAcard Z hZ hZcard
  have hP : 1≤P:=hP₀.trans hPP
  let U : ℝ:=∏i,Hcap i
  let V : ℝ:=∏i,Gcap i
  let Q : ℝ:=∏i,M i
  have hU : 0≤U:=Finset.prod_nonneg (fun i _=>(hHpos i).le)
  have hV : 0≤V:=Finset.prod_nonneg (fun i _=>(hGpos i).le)
  have hQ : 0≤Q:=Finset.prod_nonneg (fun i _=>zero_le_one.trans (hM i))
  have hHC : ((Fintype.piFinset H).card:ℝ)≤U:=pi_card_le H Hcap hHcard
  have hGC : ((Fintype.piFinset G).card:ℝ)≤V:=pi_card_le G Gcap hGcard
  have hAC : ((Fintype.piFinset A).card:ℝ)≤Q:=pi_card_le A M hAcard
  have hw : (weightedCount H A (fun _=>progressionPhase (J:=(k-(j+r))/2) (2*k) 2):ℝ)≤
      C₁*P^(ε/2)*(U*Q):=by
    simpa only [Finset.prod_mul_distrib] using hweight P hP H A Hcap M hHpos hHcard
      (fun i h hh=>(hH i h hh).1) hM hMP (fun i m hm=>(hA i m hm).2) hAcard
  have hb:=hsource P hPP H A G hH hG
    (fun i m hm=>⟨(hA i m hm).1,(hA i m hm).2.trans (hMP i)⟩) Z hZ
  apply hb.trans
  calc
    _ ≤ C₀*P^(ε/2)*V*(P*(C₁*P^(ε/2)*(U*Q))+U*Q^2):=by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hGC (by positivity)
      · exact add_le_add
          (mul_le_mul hZcard hw (Nat.cast_nonneg _) (zero_le_one.trans hP))
          (by gcongr)
      · positivity
      · positivity
    _ = C₀*P^(ε/2)*(C₁*P^(ε/2)*(P*U*V*Q)+1*(U*V*Q^2)):=by ring
    _ ≤ (C₀*(C₁+1))*P^ε*((P*U*V*Q)+(U*V*Q^2)):=
      scale_split_bound hP hε hC₀.le hC₁.le (by norm_num) (by positivity) (by positivity)
    _ = _:=by dsimp [U,V,Q]; ring

#print axioms sharp_padded_second_moment_box
end Waring.PolicyCompletionSharpResidualBox
