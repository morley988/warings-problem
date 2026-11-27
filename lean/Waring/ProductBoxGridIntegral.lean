import Waring.ProductBoxGrid

/-! # Finite-grid and integral interchange for product boxes -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open SmoothMoments EndgameCompletion

theorem gridSum_sub (L M : ℕ) (f g : (Fin L → ℕ) → ℂ) :
    gridSum L M (fun x => f x-g x)=gridSum L M f-gridSum L M g := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [gridSum,ih,Finset.sum_sub_distrib]

theorem continuous_gridSum {X : Type*} [TopologicalSpace X] (L M : ℕ)
    (f : X → (Fin L → ℕ) → ℂ) (hf : ∀ y,Continuous (fun x => f x y)) :
    Continuous (fun x => gridSum L M (f x)) := by
  induction L with
  | zero => exact hf _
  | succ L ih =>
    exact continuous_finset_sum _ (fun n _ => ih _ (fun y => hf (Fin.cons n y)))

theorem gridSum_integral (L M : ℕ) (a b : ℝ) (f : ℝ → (Fin L → ℕ) → ℂ)
    (hf : ∀ y,Continuous (fun t => f t y)) :
    gridSum L M (fun y => ∫ t in Set.Icc a b,f t y)=
      ∫ t in Set.Icc a b,gridSum L M (f t) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [gridSum]
    have he (n : ℕ) := ih (fun t y => f t (Fin.cons n y)) (fun y => hf _)
    simp_rw [he]
    exact (integral_finset_sum _ (fun n _ =>
      (continuous_gridSum L M _ (fun y => hf _)).continuousOn.integrableOn_compact isCompact_Icc)).symm

def headMean {L : ℕ} (q : ℕ) (c : (Fin (L+1) → ℕ) → ℂ) (y : Fin L → ℕ) : ℂ :=
  periodicMean (fun n => c (Fin.cons (n+1) y)) q

theorem headMean_eq {L : ℕ} (q : ℕ) (c : (Fin (L+1) → ℕ) → ℂ) (y : Fin L → ℕ) :
    headMean q c y=(∑ n∈Finset.Icc 1 q,c (Fin.cons n y))/(q : ℂ) := by
  have he := positivePartialSum_eq_range (fun n => c (Fin.cons n y)) (q : ℝ)
  simpa only [positivePartialSum,Nat.floor_natCast,headMean,periodicMean] using
    congrArg (fun z : ℂ => z/(q : ℂ)) he.symm

theorem headMean_norm_le_one {L q : ℕ} (hq : 0<q) {c : (Fin (L+1) → ℕ) → ℂ}
    (hc : ∀ x,‖c x‖≤1) (y : Fin L → ℕ) : ‖headMean q c y‖≤1 :=
  norm_periodicMean_le hq (fun _ => hc _)

theorem headMean_periodic {L q : ℕ} {c : (Fin (L+1) → ℕ) → ℂ}
    (hc : GridPeriodic (L+1) q c) : GridPeriodic L q (headMean q c) := by
  have hh := GridPeriodic_sum L q (Finset.Icc 1 q)
    (fun n y => c (Fin.cons n y)) (fun n _ => hc.2 n)
  have he : headMean q c=(fun y => (∑ n∈Finset.Icc 1 q,c (Fin.cons n y))/(q : ℂ)) :=
    funext (headMean_eq q c)
  rw [he]
  simpa only [div_eq_mul_inv] using GridPeriodic_mul_const L q hh (q : ℂ)⁻¹

theorem gridMean_headMean (L q : ℕ) (c : (Fin (L+1) → ℕ) → ℂ) :
    gridMean L q (headMean q c)=gridMean (L+1) q c := by
  have he : headMean q c=(fun y => (∑ n∈Finset.Icc 1 q,c (Fin.cons n y))/(q : ℂ)) :=
    funext (headMean_eq q c)
  rw [he]
  unfold gridMean
  simp_rw [div_eq_mul_inv]
  rw [gridSum_mul_const,gridSum_sum]
  simp only [gridSum,pow_succ,mul_inv_rev]
  ring

def consEmbedding (L : ℕ) : ℕ × (Fin L → ℕ) ↪ (Fin (L+1) → ℕ) where
  toFun z := Fin.cons z.1 z.2
  inj' := by
    intro a b h
    apply Prod.ext
    · exact congrFun h 0
    · funext j
      exact congrFun h j.succ

theorem finiteTuples_succ (S : Finset ℕ) (L : ℕ) :
    finiteTuples S (L+1)=(S.product (finiteTuples S L)).map (consEmbedding L) := by
  ext x
  constructor
  · intro hx
    refine Finset.mem_map.mpr ⟨(x 0,fun i => x i.succ),?_,?_⟩
    · exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hx 0,
        Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mp hx i.succ)⟩
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  · intro hx
    obtain ⟨⟨a,y⟩,hy,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨ha,hy⟩ := Finset.mem_product.mp hy
    apply Fintype.mem_piFinset.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ha
    · exact Fintype.mem_piFinset.mp hy j

theorem gridSum_eq_finiteTuples (L M : ℕ) (f : (Fin L → ℕ) → ℂ) :
    gridSum L M f=∑ x∈finiteTuples (Finset.Icc 1 M) L,f x := by
  induction L with
  | zero =>
    have he : finiteTuples (Finset.Icc 1 M) 0={Fin.elim0} := by
      ext x
      simp only [finiteTuples,Fintype.mem_piFinset,Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _,fun _ i => Fin.elim0 i⟩
    simp [gridSum,he]
  | succ L ih =>
    rw [finiteTuples_succ,Finset.sum_map]
    have hh := Finset.sum_product (Finset.Icc 1 M) (finiteTuples (Finset.Icc 1 M) L)
      (fun z => f (consEmbedding L z))
    change (∑ x∈(Finset.Icc 1 M).product (finiteTuples (Finset.Icc 1 M) L),
      f (consEmbedding L x)) = _ at hh
    rw [hh]
    simp only [gridSum,consEmbedding,Function.Embedding.coeFn_mk,ih]

#print axioms gridSum_eq_finiteTuples
end Waring.ProductBox
