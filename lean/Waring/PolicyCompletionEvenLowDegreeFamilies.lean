import Waring.PolicyCompletionEvenLowDegreePolynomial
import Waring.SeedCompletionTerminalCurves

/-! # Sharp low even degree collisions, with the literal polynomial diagonal -/
noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionEvenLowDegreeFamilies
open Polynomial PolicyCompletionEvenLowDegreePolynomial PolicyCompletionEvenLowDegreePairs
open PolicyCompletionEvenLowDegreeBounds SeedCompletionCurveFamilies SeedCompletionTerminalCurves
open AuxiliaryL2Grouping

def polynomialPairs (f g : Polynomial ℤ) (Z : Finset ℕ) : Finset (ℕ×ℕ):=
  (Z×ˢZ).filter (fun zw=>f.eval (zw.1:ℤ)=g.eval (zw.2:ℤ))

theorem polynomialPairs_to_quadratic (f g : Polynomial ℤ) (Z : Finset ℕ)
    (hf : f.natDegree≤2) (hg : g.natDegree≤2)
    (hf1 : f.coeff 1=0) (hg1 : g.coeff 1=0) (ha : f.coeff 2=g.coeff 2) :
    (polynomialPairs f g Z).card≤
      (quadraticPairs (f.coeff 2) (f.coeff 0) (g.coeff 0)
        (Z.image (fun z : ℕ=>(z:ℤ))) (Z.image (fun z : ℕ=>(z:ℤ)))).card := by
  apply Finset.card_le_card_of_injOn (fun zw : ℕ×ℕ=>((zw.1:ℤ),(zw.2:ℤ)))
  · intro zw hzw
    obtain ⟨hz,he⟩:=Finset.mem_filter.mp hzw
    obtain ⟨hz,hw⟩:=Finset.mem_product.mp hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hz,Finset.mem_image_of_mem _ hw⟩,?_⟩
    rw [quadratic_eval f hf hf1,quadratic_eval g hg hg1,←ha] at he
    exact he
  · intro x hx y hy he
    exact Prod.ext (Int.ofNat_inj.mp (congrArg Prod.fst he))
      (Int.ofNat_inj.mp (congrArg Prod.snd he))

theorem polynomialPairs_to_quartic (f g : Polynomial ℤ) (Z : Finset ℕ)
    (hf : f.natDegree≤4) (hg : g.natDegree≤4)
    (hf1 : f.coeff 1=0) (hg1 : g.coeff 1=0) (hf3 : f.coeff 3=0) (hg3 : g.coeff 3=0)
    (ha : f.coeff 4=g.coeff 4) :
    (polynomialPairs f g Z).card≤
      (quarticPairs (f.coeff 4) (f.coeff 2) (f.coeff 0) (g.coeff 2) (g.coeff 0)
        (Z.image (fun z : ℕ=>(z:ℤ))) (Z.image (fun z : ℕ=>(z:ℤ)))).card := by
  apply Finset.card_le_card_of_injOn (fun zw : ℕ×ℕ=>((zw.1:ℤ),(zw.2:ℤ)))
  · intro zw hzw
    obtain ⟨hz,he⟩:=Finset.mem_filter.mp hzw
    obtain ⟨hz,hw⟩:=Finset.mem_product.mp hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hz,Finset.mem_image_of_mem _ hw⟩,?_⟩
    rw [quartic_eval f hf hf1 hf3,quartic_eval g hg hg1 hg3,←ha] at he
    exact he
  · intro x hx y hy he
    exact Prod.ext (Int.ofNat_inj.mp (congrArg Prod.fst he))
      (Int.ofNat_inj.mp (congrArg Prod.snd he))

theorem unequal_polynomial_pairs {L ε : ℝ} (hL : 0≤L) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,1≤P→∀(f g : Polynomial ℤ) (d : ℕ),
      (d=2 ∨ d=4)→f.natDegree=d→g.natDegree=d→
      f.leadingCoeff=g.leadingCoeff→0<f.leadingCoeff→
      (∀i,0≤f.coeff i)→(∀i,0≤g.coeff i)→
      f.eval (-1)=f.eval 1→g.eval (-1)=g.eval 1→
      ((f.eval 1:ℤ):ℝ)≤P^L→((g.eval 1:ℤ):ℝ)≤P^L→f≠g→
      ∀Z : Finset ℕ,(∀z∈Z,0<z)→
      ((polynomialPairs f g Z).card:ℝ)≤C*P^ε := by
  obtain ⟨C₂,hC₂,h₂⟩:=quadratic_unequal_uniform hL hε
  obtain ⟨C₄,hC₄,h₄⟩:=quartic_unequal_uniform hL hε
  refine ⟨C₂+C₄,add_pos hC₂ hC₄,?_⟩
  intro P hP f g d hd hf hg ha hapos hfn hgn hfe hge hfsize hgsize hne Z hZ
  have hdf : f.natDegree≤4:=by omega
  have hdg : g.natDegree≤4:=by omega
  obtain ⟨hf1,hf3⟩:=even_low_coefficients f hdf hfn hfe
  obtain ⟨hg1,hg3⟩:=even_low_coefficients g hdg hgn hge
  have hfc (i : ℕ) : |(f.coeff i:ℝ)|≤P^L:=by
    rw [abs_of_nonneg (by exact_mod_cast hfn i)]
    have hi : (f.coeff i:ℝ)≤((f.eval 1:ℤ):ℝ):=by
      exact_mod_cast nonnegative_coefficient_le_eval_one f hfn i
    exact hi.trans hfsize
  have hgc (i : ℕ) : |(g.coeff i:ℝ)|≤P^L:=by
    rw [abs_of_nonneg (by exact_mod_cast hgn i)]
    have hi : (g.coeff i:ℝ)≤((g.eval 1:ℤ):ℝ):=by
      exact_mod_cast nonnegative_coefficient_le_eval_one g hgn i
    exact hi.trans hgsize
  have hZa : ∀z∈Z.image (fun z : ℕ=>(z:ℤ)),0<z:=by
    intro z hz
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    exact_mod_cast hZ x hx
  rcases hd with rfl|rfl
  · have heada : f.coeff 2=g.coeff 2:=by simpa only [leadingCoeff,hf,hg] using ha
    have hapos' : 0<f.coeff 2:=by simpa only [leadingCoeff,hf] using hapos
    have hneq : f.coeff 0≠g.coeff 0:=fun he=>hne (quadratic_ext f g hf.le hg.le hf1 hg1 heada he)
    have hb:=h₂ P hP _ _ _ hapos'.ne' (hfc 0) (hgc 0) hneq
      (Z.image (fun z : ℕ=>(z:ℤ))) (Z.image (fun z : ℕ=>(z:ℤ)))
    have hc : ((polynomialPairs f g Z).card:ℝ)≤
        ((quadraticPairs (f.coeff 2) (f.coeff 0) (g.coeff 0)
          (Z.image (fun z : ℕ=>(z:ℤ))) (Z.image (fun z : ℕ=>(z:ℤ)))).card:ℝ):=by
      exact_mod_cast polynomialPairs_to_quadratic f g Z hf.le hg.le hf1 hg1 heada
    exact (hc.trans hb).trans (by gcongr; linarith)
  · have heada : f.coeff 4=g.coeff 4:=by simpa only [leadingCoeff,hf,hg] using ha
    have hapos' : 0<f.coeff 4:=by simpa only [leadingCoeff,hf] using hapos
    have hneq : ¬(f.coeff 2=g.coeff 2 ∧ f.coeff 0=g.coeff 0):=by
      rintro ⟨hb,hc⟩
      exact hne (quartic_ext f g hf.le hg.le hf1 hg1 hf3 hg3 heada hb hc)
    have hb:=h₄ P hP _ _ _ _ _ hapos' (hfn 2) (hgn 2) (hfc 4) (hfc 2) (hfc 0)
      (hgc 2) (hgc 0) hneq (Z.image (fun z : ℕ=>(z:ℤ))) (Z.image (fun z : ℕ=>(z:ℤ))) hZa hZa
    have hc : ((polynomialPairs f g Z).card:ℝ)≤
        ((quarticPairs (f.coeff 4) (f.coeff 2) (f.coeff 0) (g.coeff 2) (g.coeff 0)
          (Z.image (fun z : ℕ=>(z:ℤ))) (Z.image (fun z : ℕ=>(z:ℤ)))).card:ℝ):=by
      exact_mod_cast polynomialPairs_to_quartic f g Z hf.le hg.le hf1 hg1 hf3 hg3 heada
    exact (hc.trans hb).trans (by gcongr; linarith)

#print axioms unequal_polynomial_pairs
end Waring.PolicyCompletionEvenLowDegreeFamilies
