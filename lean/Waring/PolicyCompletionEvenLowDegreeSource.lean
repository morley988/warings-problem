import Waring.PolicyCompletionEvenLowDegreeFamilies
import Waring.SeedCompletionTerminalSparse

/-! # Sharp actual source second moments at residual degrees two and four -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionEvenLowDegreeSource
open Polynomial IntegerDifferencePolynomial PolicyCompletionMajorFamily
open PolicyCompletionPositivePhase PolicyCompletionPhaseContent
open PolicyCompletionEvenLowDegreeFamilies SeedCompletionTerminalPhase
open SeedCompletionCurveFamilies SeedCompletionTerminalCurves SeedCompletionProductGrouping
open SeedCompletionTerminalSecond SeedCompletionTerminalSparse AuxiliaryL2Grouping

theorem source_polynomial_even {k j : ℕ} (hj : j<k) (hd : k-j=2 ∨ k-j=4)
    (h m : Fin j→ℕ) (hm : ∀i,0<m i) :
    (powerPolynomial k (naturalParameters h m)).eval (-1)=
      (powerPolynomial k (naturalParameters h m)).eval 1 := by
  have heven : Even (k+j):=Nat.even_iff.mpr (by omega)
  have hp:=powerPolynomial_parity k (naturalParameters h m) (by
    simp only [naturalParameters,List.forall_mem_ofFn_iff]
    intro i
    exact_mod_cast (hm i).ne') 1
  simp only [naturalParameters_length,heven.neg_one_pow,one_mul] at hp
  have hc (z : ℤ) := Polynomial.eval₂_at_apply
    (p:=powerPolynomial k (naturalParameters h m)) (Int.castRingHom ℝ) z
  have hn:=hc (-1)
  have h1:=hc 1
  simp only [map_neg,map_one] at hn h1
  rw [hn,h1] at hp
  exact (Int.cast_injective (α:=ℝ)) hp

theorem same_height_collision_bound {k j : ℕ} (hj : j<k)
    (hd : k-j=2 ∨ k-j=4) {L ε : ℝ} (hL : 0≤L) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→∀h : Fin j→ℕ,(∀i,0<h i)→
      ∀B : Finset (Fin j→ℕ),(∀m∈B,∀i,0<m i)→
      ∀Z : Finset ℕ,(∀z∈Z,0<z)→(∀m∈B,(phase k h m 1:ℝ)≤P^L)→
      ((collisionPairs (B×ˢZ) (fun mz=>phase k h mz.1 mz.2)).card:ℝ)≤
        (Z.card:ℝ)*((samePolynomialPairs B (realPolynomial k h)).card:ℝ)+C*P^ε*(B.card:ℝ)^2 := by
  obtain ⟨C,hC,hpair⟩:=unequal_polynomial_pairs hL hε
  refine ⟨C,hC,?_⟩
  intro P hP h hh B hB Z hZ hsize
  let F (m : Fin j→ℕ) : Polynomial ℤ:=powerPolynomial k (naturalParameters h m)
  have hp (m) (hm : m∈B) := naturalParameters_pos h m hh (hB m hm)
  have hdeg (m) (hm : m∈B) : (F m).natDegree=k-j:=by
    dsimp only [F]
    rw [powerPolynomial_natDegree k _ (fun p hq=>⟨(hp m hm p hq).1.ne',(hp m hm p hq).2.ne'⟩)
      (by simpa using hj.le),naturalParameters_length]
  have hlead (m) (hm : m∈B) (n) (hn : n∈B) : (F m).leadingCoeff=(F n).leadingCoeff:=by
    dsimp [F]
    rw [powerPolynomial_leadingCoeff k _ (fun p hq=>⟨(hp m hm p hq).1.ne',(hp m hm p hq).2.ne'⟩)
      (by simpa using hj.le),powerPolynomial_leadingCoeff k _
      (fun p hq=>⟨(hp n hn p hq).1.ne',(hp n hn p hq).2.ne'⟩) (by simpa using hj.le)]
    simp
  have hfn (m) (hm : m∈B) (i) : 0≤(F m).coeff i:=
    powerPolynomial_coeff_nonneg k _ (fun p hq=>⟨(hp m hm p hq).1.le,(hp m hm p hq).2⟩) i
  have hc (m) (hm : m∈B) (n) (hn : n∈B) :
      ((centerPairs (phase k h) m n Z).card:ℝ)≤
        (if realPolynomial k h m=realPolynomial k h n then (Z.card:ℝ) else 0)+C*P^ε:=by
    by_cases he : realPolynomial k h m=realPolynomial k h n
    · rw [if_pos he,centerPairs_equal (phase k h) (realPolynomial k h) m n Z
        (phase_strictMono hj h n hh (hB n hn)) (realPolynomial_eval k h m)
        (realPolynomial_eval k h n) he]
      have hCP : 0≤C*P^ε:=by positivity
      linarith
    · rw [if_neg he,zero_add]
      have hne : F m≠F n:=fun heq=>he (congrArg (fun f : Polynomial ℤ=>f.map (Int.castRingHom ℝ)) heq)
      exact hpair P hP (F m) (F n) (k-j) hd (hdeg m hm) (hdeg n hn) (hlead m hm n hn)
        (powerPolynomial_leadingCoeff_pos k _ (hp m hm) (by simpa using hj.le))
        (hfn m hm) (hfn n hn) (source_polynomial_even hj hd h m (hB m hm))
        (source_polynomial_even hj hd h n (hB n hn)) (hsize m hm) (hsize n hn) hne Z hZ
  have hdiag : (∑m∈B,∑n∈B,if realPolynomial k h m=realPolynomial k h n then (Z.card:ℝ) else 0)=
      (Z.card:ℝ)*((samePolynomialPairs B (realPolynomial k h)).card:ℝ):=by
    simp only [samePolynomialPairs,Finset.card_eq_sum_ones,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,
      Nat.cast_zero,Finset.sum_filter,Finset.sum_product,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [collision_card,Nat.cast_sum]
  calc
    _ ≤ ∑m∈B,∑n∈B,((if realPolynomial k h m=realPolynomial k h n then (Z.card:ℝ) else 0)+C*P^ε):=by
      apply Finset.sum_le_sum
      intro m hm
      rw [Nat.cast_sum]
      exact Finset.sum_le_sum (fun n hn=>hc m hm n hn)
    _ = _:=by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      rw [hdiag]
      ring

theorem low_source_second_moment {k j : ℕ} (hj : j<k)
    (hd : k-j=2 ∨ k-j=4) {L ε : ℝ} (hL : 0≤L) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→∀H B : Finset (Fin j→ℕ),
      (∀h∈H,∀i,0<h i)→(∀m∈B,∀i,0<m i)→
      ∀Z : Finset ℕ,(∀z∈Z,0<z)→
      (∀h∈H,∀m∈B,∀z∈Z,((phase k h m z).natAbs:ℝ)≤P^L)→
      (∀h∈H,∀m∈B,(phase k h m 1:ℝ)≤P^L)→
      sourceSecondMoment k H B Z≤
        C*P^ε*((Z.card:ℝ)*(∑h∈H,((samePolynomialPairs B (realPolynomial k h)).card:ℝ))+
          (H.card:ℝ)*(B.card:ℝ)^2) := by
  obtain ⟨C₀,hC₀,hgroup⟩:=second_moment_divisor_product j hL (show 0<ε/2 by positivity)
  obtain ⟨C₁,hC₁,hwithin⟩:=same_height_collision_bound hj hd hL (show 0<ε/2 by positivity)
  refine ⟨C₀*(C₁+1),by positivity,?_⟩
  intro P hP H B hH hB Z hZ hsize hone
  have hb:=hgroup P hP (Fin j→ℕ) ((Fin j→ℕ)×ℕ) H (B×ˢZ)
    (fun h mz=>phase k h mz.1 mz.2) id Function.injective_id.injOn
    (by
      intro h hh mz hmz
      obtain ⟨hm,hz⟩:=Finset.mem_product.mp hmz
      exact ⟨(phase_pos hj h mz.1 (hH h hh) (hB _ hm) (hZ _ hz)).ne',hsize h hh _ hm _ hz⟩)
    (by
      intro h hh mz hmz i
      exact height_dvd_phase k h mz.1 (hB _ (Finset.mem_product.mp hmz).1) mz.2 i)
  apply hb.trans
  calc
    _ ≤ C₀*P^(ε/2)*((Z.card:ℝ)*(∑h∈H,((samePolynomialPairs B (realPolynomial k h)).card:ℝ))+
        C₁*P^(ε/2)*(H.card:ℝ)*(B.card:ℝ)^2):=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (Finset.sum_le_sum (fun h hh=>hwithin P hP h (hH h hh) B hB Z hZ (hone h hh))).trans_eq
      rw [Finset.sum_add_distrib,←Finset.mul_sum]
      simp only [Finset.sum_const,nsmul_eq_mul]
      ring
    _ = C₀*P^(ε/2)*(C₁*P^(ε/2)*((H.card:ℝ)*(B.card:ℝ)^2)+
        1*((Z.card:ℝ)*(∑h∈H,((samePolynomialPairs B (realPolynomial k h)).card:ℝ)))):=by ring
    _ ≤ (C₀*(C₁+1))*P^ε*(((H.card:ℝ)*(B.card:ℝ)^2)+
        ((Z.card:ℝ)*(∑h∈H,((samePolynomialPairs B (realPolynomial k h)).card:ℝ)))):=
      scale_split_bound hP hε hC₀.le hC₁.le (by norm_num) (by positivity) (by positivity)
    _ = _:=by ring

#print axioms low_source_second_moment
end Waring.PolicyCompletionEvenLowDegreeSource
