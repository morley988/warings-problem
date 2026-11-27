import Waring.ProductBoxIntegral
import Waring.EvenMoments

/-! # Literal finite product grids and periodic means -/

noncomputable section
open scoped BigOperators
namespace Waring.ProductBox
open SmoothMoments

def gridSum : (L : ℕ) → ℕ → ((Fin L → ℕ) → ℂ) → ℂ
  | 0,_,f => f Fin.elim0
  | L+1,M,f => ∑ n∈Finset.Icc 1 M,gridSum L M (fun y => f (Fin.cons n y))

def gridMean (L q : ℕ) (c : (Fin L → ℕ) → ℂ) : ℂ := gridSum L q c/(q : ℂ)^L

def GridPeriodic : (L q : ℕ) → ((Fin L → ℕ) → ℂ) → Prop
  | 0,_,_ => True
  | L+1,q,c => (∀ y,Function.Periodic (fun n => c (Fin.cons n y)) q) ∧
      ∀ n,GridPeriodic L q (fun y => c (Fin.cons n y))

theorem gridSum_congr (L M : ℕ) {f g : (Fin L → ℕ) → ℂ}
    (h : ∀ x,(∀ i,x i ∈ Finset.Icc 1 M) → f x=g x) :
    gridSum L M f=gridSum L M g := by
  induction L with
  | zero => exact h _ (by intro i; exact Fin.elim0 i)
  | succ L ih =>
    apply Finset.sum_congr rfl
    intro n hn
    apply ih
    intro y hy
    apply h
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hn
    · exact hy j

theorem gridSum_const (L M : ℕ) (c : ℂ) : gridSum L M (fun _ => c)=(M : ℂ)^L*c := by
  induction L with
  | zero => simp [gridSum]
  | succ L ih =>
    simp only [gridSum,ih,Finset.sum_const,nsmul_eq_mul]
    simp only [Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_id,pow_succ]
    ring

theorem gridSum_add (L M : ℕ) (f g : (Fin L → ℕ) → ℂ) :
    gridSum L M (fun x => f x+g x)=gridSum L M f+gridSum L M g := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [gridSum,ih,Finset.sum_add_distrib]

theorem gridSum_mul_const (L M : ℕ) (f : (Fin L → ℕ) → ℂ) (c : ℂ) :
    gridSum L M (fun x => f x*c)=gridSum L M f*c := by
  induction L with
  | zero => rfl
  | succ L ih => simp only [gridSum,ih,Finset.sum_mul]

theorem gridSum_const_mul (L M : ℕ) (f : (Fin L → ℕ) → ℂ) (c : ℂ) :
    gridSum L M (fun x => c*f x)=c*gridSum L M f := by
  simp_rw [mul_comm c]
  exact gridSum_mul_const L M f c

theorem gridSum_sum {ι : Type*} (L M : ℕ) (S : Finset ι) (f : ι → (Fin L → ℕ) → ℂ) :
    gridSum L M (fun x => ∑ i∈S,f i x)=∑ i∈S,gridSum L M (f i) := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp only [gridSum,ih]
    exact Finset.sum_comm

theorem gridSum_norm_le (L M : ℕ) {B : ℝ} (hB : 0≤B)
    {f : (Fin L → ℕ) → ℂ} (hf : ∀ x,(∀ i,x i ∈ Finset.Icc 1 M) → ‖f x‖≤B) :
    ‖gridSum L M f‖≤B*(M : ℝ)^L := by
  induction L with
  | zero => simpa [gridSum] using hf Fin.elim0 (by intro i; exact Fin.elim0 i)
  | succ L ih =>
    calc
      _ ≤ ∑ n∈Finset.Icc 1 M,‖gridSum L M (fun y => f (Fin.cons n y))‖ := norm_sum_le _ _
      _ ≤ ∑ _n∈Finset.Icc 1 M,B*(M : ℝ)^L := by
        apply Finset.sum_le_sum
        intro n hn
        apply ih
        intro y hy
        apply hf
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hn
        · exact hy j
      _ = _ := by simp [Nat.card_Icc,pow_succ]; ring

theorem gridMean_norm_le_one (L q : ℕ) (hq : 0<q) {c : (Fin L → ℕ) → ℂ}
    (hc : ∀ x,‖c x‖≤1) : ‖gridMean L q c‖≤1 := by
  rw [gridMean,norm_div,norm_pow,Complex.norm_natCast]
  apply (div_le_one (pow_pos (by exact_mod_cast hq) L)).mpr
  simpa only [one_mul] using gridSum_norm_le L q zero_le_one (fun x _ => hc x)

theorem GridPeriodic_sum {ι : Type*} (L q : ℕ) (S : Finset ι)
    (f : ι → (Fin L → ℕ) → ℂ) (hf : ∀ i∈S,GridPeriodic L q (f i)) :
    GridPeriodic L q (fun x => ∑ i∈S,f i x) := by
  induction L with
  | zero => trivial
  | succ L ih =>
    constructor
    · intro y n
      apply Finset.sum_congr rfl
      intro i hi
      exact (hf i hi).1 y n
    · intro n
      apply ih
      intro i hi
      exact (hf i hi).2 n

theorem GridPeriodic_mul_const (L q : ℕ) {c : (Fin L → ℕ) → ℂ}
    (hc : GridPeriodic L q c) (a : ℂ) : GridPeriodic L q (fun x => c x*a) := by
  induction L with
  | zero => trivial
  | succ L ih =>
    exact ⟨fun y n => congrArg (fun z => z*a) (hc.1 y n),fun n => ih (hc.2 n)⟩

#print axioms gridSum_norm_le
end Waring.ProductBox
