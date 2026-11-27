import Waring.SeedCompletionNinthTripleIdentity
import Waring.SeedCompletionNinthTripleCount
import Waring.SeedCompletionPhaseSize

/-! # Actual degree-nine third-phase second moment on source-sized boxes -/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNinthTripleBox
open SeedCompletionNinthTriple SeedCompletionNinthTripleCount IntegerDifferencePolynomial
open SeedCompletionNinthDouble (Pair)

def actualSum (H : Finset Heights) (B : Finset Pair) (Z : Finset ℕ) (α : ℝ) : ℂ :=
  ∑ x ∈ H ×ˢ (B ×ˢ Z),fourier
    ((powerPolynomial 9 [((x.1.2 : ℤ),1),((x.1.1.2 : ℤ),(x.2.1.2 : ℤ)),
      ((x.1.1.1 : ℤ),(x.2.1.1 : ℤ))]).eval (x.2.2 : ℤ)) (α : AddCircle (1 : ℝ))

theorem actual_second_on_box {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∃ P₀ : ℝ,1 ≤ P₀ ∧ ∀ P : ℝ,P₀ ≤ P →
      ∀ (H : Finset Heights) (B : Finset Pair) (Z : Finset ℕ),
      (∀ h ∈ H,0 < h.1.1 ∧ 0 < h.1.2 ∧ 0 < h.2) →
      (∀ m ∈ B,0 < m.1 ∧ 0 < m.2) → (∀ z ∈ Z,0 < z) →
      (∀ h ∈ H,(h.1.1 : ℝ) ≤ P ∧ (h.1.2 : ℝ) ≤ P ∧ (h.2 : ℝ) ≤ P) →
      (∀ m ∈ B,(m.1 : ℝ) ≤ P ∧ (m.2 : ℝ) ≤ P) →
      (∀ z ∈ Z,(z : ℝ) ≤ P) →
      (B.card : ℝ) ≤ P^(1/3 : ℝ) → (Z.card : ℝ) ≤ P →
      (∫ α in (0 : ℝ)..1,‖actualSum H B Z α‖^2) ≤
        C*P^(1+ε)*(H.card : ℝ)*(B.card : ℝ) := by
  obtain ⟨P₀,hP₀,hsize⟩ := powerPolynomial_magnitude_polynomial_bound 9 3
  obtain ⟨C,hC,hbound⟩ := second_moment (L := 91) (by norm_num) hε
  refine ⟨1748*C,by positivity,P₀,hP₀,?_⟩
  intro P hPP₀ H B Z hHp hBp hZp hHb hBb hZb hBc hZc
  have hP : 1 ≤ P := hP₀.trans hPP₀
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hs : ∀ x ∈ H ×ˢ (B ×ˢ Z),((indexPhase x).natAbs : ℝ) ≤ P^(91 : ℝ) := by
    intro x hx
    rcases Finset.mem_product.mp hx with ⟨hh,hmz⟩
    rcases Finset.mem_product.mp hmz with ⟨hm,hz⟩
    change ((phase x.1 x.2.1 x.2.2 : ℤ).natAbs : ℝ) ≤ _
    rw [phase_eq_powerPolynomial _ _ _ (hBp _ hm).1 (hBp _ hm).2]
    apply hsize P hPP₀ _ (by simp)
    · intro p hp
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl | rfl
      · norm_num
      · change (x.2.1.2 : ℤ) ≠ 0
        exact_mod_cast (hBp _ hm).2.ne'
      · change (x.2.1.1 : ℤ) ≠ 0
        exact_mod_cast (hBp _ hm).1.ne'
    · intro p hp
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl | rfl | rfl
      · simpa using And.intro (hHb _ hh).2.2 hP
      · simpa using And.intro (hHb _ hh).2.1 (hBb _ hm).2
      · simpa using And.intro (hHb _ hh).1 (hBb _ hm).1
    · simpa using hZb _ hz
  have hb := hbound P hP H B Z hHp (fun z hz => ⟨hZp z hz,hZb z hz⟩) hs
  have hcurve : (B.card : ℝ)*P^(2/3 : ℝ) ≤ P := by
    calc
      _ ≤ P^(1/3 : ℝ)*P^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right hBc (by positivity)
      _ = P := by rw [← Real.rpow_add hPpos]; norm_num
  have hc : 2*(Z.card : ℝ)+(B.card : ℝ)*(1746*P^(2/3 : ℝ)) ≤ 1748*P := by nlinarith
  have heq (α : ℝ) : actualSum H B Z α =
      ∑ x ∈ H ×ˢ (B ×ˢ Z),fourier (indexPhase x) (α : AddCircle (1 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hm := (Finset.mem_product.mp (Finset.mem_product.mp hx).2).1
    rw [← phase_eq_powerPolynomial _ _ _ (hBp _ hm).1 (hBp _ hm).2]
    rfl
  simp_rw [heq]
  calc
    _ ≤ _ := hb
    _ ≤ C*P^ε*(H.card : ℝ)*(B.card : ℝ)*(1748*P) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by rw [Real.rpow_add hPpos,Real.rpow_one]; ring

#print axioms actual_second_on_box
end Waring.SeedCompletionNinthTripleBox
