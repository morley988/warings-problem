import Waring.PolicyCompletionMajorBoxRanges
import Waring.SeedCompletionEnlargedBackward
import Waring.PolicyCompletionNextDomain
import Waring.SeedCompletionPhasePermutation

/-! # Literal natural boxes for every centered-difference stage -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNaturalBox
open IntegerDifferencePolynomial PolicyCompletionMajorFamily PolicyCompletionMajorBoxRanges
open CartesianProductSampling PolicyCompletionHolder PolicyCompletionSourceMajor
open EndgameCompletion SmoothMoments SeedCompletionBackwardAggregate
open SeedCompletionBackwardMoments PolicyCompletionNextDomain

abbrev NaturalLabel (j : ℕ) := (Fin j → ℕ) × (Fin j → ℕ)
abbrev NaturalNextLabel (j : ℕ) := Σ _ : NaturalLabel j × ℕ,ℤ × ℤ

def naturalPhase {j : ℕ} (k : ℕ) (p : NaturalLabel j × ℕ) : ℤ :=
  (powerPolynomial k (naturalParameters p.1.1 p.1.2)).eval (p.2:ℤ)

def naturalBoxLabels {j : ℕ} (k : ℕ) (L Q R : ℝ) (M : Fin j → ℝ) :
    Finset (NaturalLabel j) :=
  positiveBox (boxHeightBounds k L M) ×ˢ boxCoefficientTuples Q R M

def naturalBoxDomain {j : ℕ} (k : ℕ) (L Q R : ℝ) (M : Fin j → ℝ) :
    Finset (NaturalLabel j × ℕ) := naturalBoxLabels k L Q R M ×ˢ ordinaryNumbers L

theorem integerPolynomialWeyl_eq_frequency (f : Polynomial ℤ) (L α : ℝ) :
    integerPolynomialWeyl f L α=
      frequencySum (ordinaryNumbers L) (fun n => f.eval (n:ℤ)) α := by
  unfold integerPolynomialWeyl frequencySum
  apply Finset.sum_congr rfl
  intro n _
  rw [Polynomial.eval_natCast_map]
  exact exp_linear_eq_fourier α _

theorem boxSourceFamily_eq_frequency {j : ℕ} (k : ℕ) (L Q R : ℝ)
    (M : Fin j → ℝ) (α : ℝ) :
    boxSourceFamily k L Q R M α=
      frequencySum (naturalBoxDomain k L Q R M) (naturalPhase k) α := by
  classical
  simp only [boxSourceFamily,sourceFamily,integerPolynomialWeyl_eq_frequency,
    naturalBoxDomain,naturalBoxLabels,frequencySum,Finset.sum_product,naturalPhase]

def nextNaturalEncode {j : ℕ} (p : NaturalNextLabel j) : NaturalLabel (j+1) × ℕ :=
  ((Fin.cons p.2.2.toNat (fun i => 2*p.1.1.1 i),Fin.cons p.1.2 p.1.1.2),p.2.1.toNat)

theorem naturalParameters_next {j : ℕ} (h m : Fin j → ℕ) (t w : ℕ) :
    naturalParameters (Fin.cons t (fun i => 2*h i)) (Fin.cons w m)=
      ((t:ℤ),(w:ℤ))::doubleHeights (naturalParameters h m) := by
  simp [naturalParameters,List.ofFn_succ,doubleHeights,List.map_ofFn,Function.comp_def]

theorem nextNaturalEncode_frequency {j : ℕ} (k : ℕ) (p : NaturalNextLabel j)
    (hx : 0≤p.2.1) (ht : 0≤p.2.2) :
    naturalPhase k (nextNaturalEncode p)=
      aggregateNextPhase k (fun c : NaturalLabel j × ℕ => naturalParameters c.1.1 c.1.2)
        (fun c => (c.2:ℤ)) p := by
  simp only [naturalPhase,nextNaturalEncode,naturalParameters_next,
    Int.toNat_of_nonneg hx,Int.toNat_of_nonneg ht,
    aggregateNextPhase,nextIntegerPhase]

theorem nextNaturalEncode_injOn {j : ℕ} (k : ℕ) (C : Finset (NaturalLabel j))
    (W : Finset ℕ) (N : ℤ) :
    Set.InjOn (@nextNaturalEncode j)
      (↑(aggregateNextDomain (C ×ˢ W) (fun p => (p.2:ℤ)) N k) : Set (NaturalNextLabel j)) := by
  intro p hp q hq heq
  have hp' := Finset.mem_product.mp (Finset.mem_sigma.mp hp).2
  have hq' := Finset.mem_product.mp (Finset.mem_sigma.mp hq).2
  have hpx : 0≤p.2.1 := le_trans (by norm_num) (Finset.mem_Icc.mp hp'.1).1
  have hpt : 0≤p.2.2 := le_trans (by norm_num) (Finset.mem_Icc.mp hp'.2).1
  have hqx : 0≤q.2.1 := le_trans (by norm_num) (Finset.mem_Icc.mp hq'.1).1
  have hqt : 0≤q.2.2 := le_trans (by norm_num) (Finset.mem_Icc.mp hq'.2).1
  have hh : p.1.1.1=q.1.1.1 := by
    funext i
    have H := congrArg (fun x : NaturalLabel (j+1) × ℕ => x.1.1 i.succ) heq
    change 2*p.1.1.1 i=2*q.1.1.1 i at H
    omega
  have hm : p.1.1.2=q.1.1.2 := by
    funext i
    exact congrArg (fun x : NaturalLabel (j+1) × ℕ => x.1.2 i.succ) heq
  have hw : p.1.2=q.1.2 :=
    congrArg (fun x : NaturalLabel (j+1) × ℕ => x.1.2 0) heq
  have ht : p.2.2=q.2.2 := by
    have H := congrArg (fun x : NaturalLabel (j+1) × ℕ => x.1.1 0) heq
    change p.2.2.toNat=q.2.2.toNat at H
    omega
  have hx : p.2.1=q.2.1 := by
    have H := congrArg Prod.snd heq
    change p.2.1.toNat=q.2.1.toNat at H
    omega
  exact Sigma.ext (Prod.ext (Prod.ext hh hm) hw) (heq_of_eq (Prod.ext hx ht))

#print axioms boxSourceFamily_eq_frequency
#print axioms nextNaturalEncode_injOn
end Waring.SeedCompletionNaturalBox
