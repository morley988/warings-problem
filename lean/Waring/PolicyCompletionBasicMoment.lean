import Waring.PolicyCompletionBasicCubic

/-!
# The actual second coefficient moment and its cubic reduction

The finite block is arbitrary and every phase and modulation is literal.
Pair expansion removes the common modulation before the geometric estimate;
the diagonal is counted exactly. This is the first stage of VW95 Lemma4.3
for the coefficient sums themselves, not only an abstract reciprocal sum.
-/

noncomputable section
open scoped BigOperators ComplexConjugate Classical
namespace Waring.PolicyCompletionBasicMoment
open RationalHeight QuadraticModulation CoefficientPower PolicyCompletionBasicCubic

def basicMoment (A : Finset ℕ) (d H J : ℕ) (α : ℝ) (σ : ℕ→ℝ) : ℝ :=
  ∑h∈Finset.Icc 1 H,∑j∈Finset.range J,
    ‖coefficientWeyl A d (α*(h : ℝ)^3*((j : ℝ)+σ h))‖^2

def pairDifference (d : ℕ) (p : ℕ×ℕ) : ℝ := (p.1 : ℝ)^d-(p.2 : ℝ)^d
def offPairs (A : Finset ℕ) : Finset (ℕ×ℕ) := (A×ˢA).filter fun p=>p.1≠p.2

theorem sampled_block_pair_identity (A : Finset ℕ) (d J : ℕ) (β t : ℝ) :
    ((∑j∈Finset.range J,‖coefficientWeyl A d (β*((j : ℝ)+t))‖^2 : ℝ) : ℂ)=
      ∑p∈A×ˢA,e (β*t*pairDifference d p)*
        ∑j∈Finset.range J,e (β*pairDifference d p*(j : ℝ)) := by
  rw [Complex.ofReal_sum]
  simp only [coefficientWeyl,norm_sq_eq_pair_sum,e_mul_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← e_add]
  congr 1
  dsimp [pairDifference]
  ring

theorem sampled_block_le_pair_kernel (A : Finset ℕ) (d J : ℕ) (β t : ℝ) :
    (∑j∈Finset.range J,‖coefficientWeyl A d (β*((j : ℝ)+t))‖^2)≤
      ∑p∈A×ˢA,linearSumBound J (β*pairDifference d p) := by
  have hnonneg : 0≤∑j∈Finset.range J,‖coefficientWeyl A d (β*((j : ℝ)+t))‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    _ = ‖((∑j∈Finset.range J,‖coefficientWeyl A d (β*((j : ℝ)+t))‖^2 : ℝ) : ℂ)‖ := by
      simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnonneg]
    _ = ‖∑p∈A×ˢA,e (β*t*pairDifference d p)*
        ∑j∈Finset.range J,e (β*pairDifference d p*(j : ℝ))‖ := by
      rw [sampled_block_pair_identity]
    _ ≤ ∑p∈A×ˢA,‖e (β*t*pairDifference d p)*
        ∑j∈Finset.range J,e (β*pairDifference d p*(j : ℝ))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul,norm_e,one_mul]
      simpa only [e,Int.cast_zero,add_zero] using
        norm_exp_linear_sum_le 0 J (β*pairDifference d p)

theorem basicMoment_le_pair_kernel (A : Finset ℕ) (d H J : ℕ) (α : ℝ) (σ : ℕ→ℝ) :
    basicMoment A d H J α σ≤
      ∑p∈A×ˢA,∑h∈Finset.Icc 1 H,linearSumBound J (α*pairDifference d p*(h : ℝ)^3) := by
  calc
    _ ≤ ∑h∈Finset.Icc 1 H,∑p∈A×ˢA,linearSumBound J ((α*(h : ℝ)^3)*pairDifference d p) :=
      Finset.sum_le_sum fun h _ => sampled_block_le_pair_kernel A d J _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro h hh
      congr 1
      ring

/-- The diagonal contributes exactly J*H*#A. -/
theorem pair_kernel_diagonal (A : Finset ℕ) (d H J : ℕ) (α : ℝ) :
    (∑p∈A×ˢA,∑h∈Finset.Icc 1 H,linearSumBound J (α*pairDifference d p*(h : ℝ)^3))=
      (J : ℝ)*H*A.card+
        ∑p∈offPairs A,∑h∈Finset.Icc 1 H,linearSumBound J (α*pairDifference d p*(h : ℝ)^3) := by
  let f : ℕ×ℕ→ℝ := fun p=>∑h∈Finset.Icc 1 H,linearSumBound J (α*pairDifference d p*(h : ℝ)^3)
  have hdiag (p : ℕ×ℕ) (hp : p.1=p.2) : f p=(J : ℝ)*H := by
    simp [f,pairDifference,hp,linearSumBound,integerDistance,mul_comm]
  have hid (p : ℕ×ℕ) : f p=(if p.1=p.2 then (J : ℝ)*H else 0)+
      (if p.1≠p.2 then f p else 0) := by
    by_cases hp : p.1=p.2
    · simp [hp,hdiag p hp]
    · simp [hp]
  have hsumdiag : (∑p∈A×ˢA,if p.1=p.2 then (J : ℝ)*H else 0)=(J : ℝ)*H*A.card := by
    calc
      _ = ∑_x∈A,(J : ℝ)*H := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro x hx
        simp [hx]
      _ = _ := by simp [mul_comm]
  change (∑p∈A×ˢA,f p)=(J : ℝ)*H*A.card+∑p∈offPairs A,f p
  calc
    _ = ∑p∈A×ˢA,((if p.1=p.2 then (J : ℝ)*H else 0)+
        (if p.1≠p.2 then f p else 0)) := Finset.sum_congr rfl (fun p _=>hid p)
    _ = _ := by
      rw [Finset.sum_add_distrib,hsumdiag,← Finset.sum_filter]
      rfl

/-- Actual second coefficient moment after the first source resummation.
Each rational witness is constructed by Dirichlet; no estimate is an input. -/
theorem basicMoment_cubic_reduction (A : Finset ℕ) (d H J : ℕ) (α : ℝ) (σ : ℕ→ℝ)
    {Y : ℝ} (hH : 0<H) (hJ : 0<J) (hY : 0<Y)
    (hsize : 16*(H : ℝ)^3*Y≤(J : ℝ)) :
    ∃r : (ℕ×ℕ)→ℚ,
      (∀p,(r p).den≤Real.sqrt (((H : ℝ)^3*J)/Y)) ∧
      basicMoment A d H J α σ≤(J : ℝ)*H*A.card+
        (J : ℝ)*H*(offPairs A).card/Y+
        2*(J : ℝ)*H*(1+Real.log H)*
          ∑p∈offPairs A,((r p).den.divisors.card : ℝ)/
            (height ((H : ℝ)^3*J) (α*pairDifference d p))^(1/3 : ℝ) := by
  choose r hr hd hb using fun p : ℕ×ℕ =>
    cubic_geometric_bound H J hH hJ hY hsize (α*pairDifference d p)
  refine ⟨r,hd,?_⟩
  have hpair := basicMoment_le_pair_kernel A d H J α σ
  rw [pair_kernel_diagonal] at hpair
  calc
    _ ≤ (J : ℝ)*H*A.card+
        ∑p∈offPairs A,∑h∈Finset.Icc 1 H,linearSumBound J (α*pairDifference d p*(h : ℝ)^3) := hpair
    _ ≤ (J : ℝ)*H*A.card+∑p∈offPairs A,
        ((J : ℝ)*H/Y+2*(J : ℝ)*((r p).den.divisors.card : ℝ)*
          ((H : ℝ)/(height ((H : ℝ)^3*J) (α*pairDifference d p))^(1/3 : ℝ))*(1+Real.log H)) :=
      add_le_add_left (Finset.sum_le_sum fun p _=>hb p) _
    _ = _ := by
      have hterm (p : ℕ×ℕ) :
          2*(J : ℝ)*((r p).den.divisors.card : ℝ)*
              ((H : ℝ)/(height ((H : ℝ)^3*J) (α*pairDifference d p))^(1/3 : ℝ))*(1+Real.log H)=
            (2*(J : ℝ)*H*(1+Real.log H))*
              (((r p).den.divisors.card : ℝ)/(height ((H : ℝ)^3*J) (α*pairDifference d p))^(1/3 : ℝ)) := by
        ring
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,nsmul_eq_mul]
      simp_rw [hterm]
      rw [← Finset.mul_sum]
      ring

#print axioms basicMoment_le_pair_kernel
#print axioms pair_kernel_diagonal
#print axioms basicMoment_cubic_reduction
end Waring.PolicyCompletionBasicMoment
