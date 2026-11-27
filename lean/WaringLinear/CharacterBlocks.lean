import WaringLinear.FiniteGram
import WaringLinear.GramAbsorption
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Divisible-conductor blocks from finite residue-character orthogonality -/
noncomputable section
open scoped BigOperators Classical ComplexConjugate
open WaringSiegel.WSL3
namespace WaringLinear

theorem gramForm_blocks {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (tag : ι→β) (A : ι→ι→ℂ) (w : ι→ℂ) :
    gramForm (fun a b => if tag a=tag b then A a b else 0) w =
    ∑c:β,gramForm (fun a b:{i // tag i=c} => A a.val b.val) (fun a =>w a.val) := by
  unfold gramForm
  rw [←sum_fibers_eq tag (fun i => ∑j,conj (w i)*w j*(if tag i=tag j then A i j else 0))]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr (by ext i; simp)
  intro i _
  rw [←sum_fibers_eq tag (fun j => conj (w i.val)*w j*(if tag i.val=tag j then A i.val j else 0))]
  simp only [i.property]
  rw [Finset.sum_eq_single c]
  · apply Finset.sum_congr (by ext j; simp)
    intro j _
    simp [j.property]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro j _
    simp [j.property,Ne.symm hb]
  · simp

/-- The quadratic form of the Gram matrix is the squared norm of the
synthesis vector. -/
theorem norm_gramForm_rows {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (v : ι→V) (w : ι→ℂ) :
    ‖gramForm (fun a b => inner ℂ (v a) (v b)) w‖=‖∑i,w i • v i‖^2 := by
  have e : gramForm (fun a b => inner ℂ (v a) (v b)) w =
      inner ℂ (∑i,w i • v i) (∑i,w i • v i) := by
    simp only [gramForm,sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [e,inner_self_eq_norm_sq_to_K]
  simp

/-- A finite family of residue characters in each block controls its
Gram operator by the largest residue occupancy times the residue group
order. The number of distinct blocks costs nothing. -/
theorem character_block_gram
    {ι β G T : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    [AddCommGroup G] [Fintype G] [Fintype T]
    (tag : ι→β) (v : T→G) (M : ℕ) (hM : ∀b, Nat.card {x:T // v x=b}≤M)
    (χ : ∀b,{i // tag i=b}→AddChar G ℂ) (hinj : ∀b,Function.Injective (χ b))
    (A : ι→ι→ℂ)
    (hcor : ∀b,∀i j:{a // tag a=b},
      A i.val j.val = ∑ x:T,conj (χ b i (v x))*χ b j (v x))
    (w : ι→ℂ) :
    ‖gramForm (fun a b => if tag a=tag b then A a b else 0) w‖ ≤
        ((M:ℝ)*Fintype.card G)*∑i,‖w i‖^2 := by
  rw [gramForm_blocks tag A w]
  calc
    _ ≤ ∑b:β,‖gramForm (fun a c:{i // tag i=b}=>A a.val c.val) (fun a=>w a.val)‖ :=
      norm_sum_le _ _
    _ ≤ ∑b:β, ((M:ℝ)*Fintype.card G)*∑i:{j // tag j=b},‖w i.val‖^2 := by
      apply Finset.sum_le_sum
      intro b _
      let row (i:{j // tag j=b}) : EuclideanSpace ℂ T :=
        (EuclideanSpace.equiv T ℂ).symm fun x => χ b i (v x)
      have eqK (i j:{a // tag a=b}) : A i.val j.val=inner ℂ (row i) (row j) := by
        rw [hcor b i j,PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro x _
        change conj (χ b i (v x))*χ b j (v x)=χ b j (v x)*conj (χ b i (v x))
        ring
      simp_rw [eqK]
      rw [norm_gramForm_rows,EuclideanSpace.norm_sq_eq]
      have H := sampled_character_synthesis v M hM (χ b) (hinj b) (fun i=>w i.val)
      convert H using 1
      apply Finset.sum_congr rfl
      intro x _
      congr 2
      change (EuclideanSpace.equiv T ℂ (∑i,w i.val • row i)) x=_
      rw [map_sum,Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ = _ := by
      rw [←Finset.mul_sum]
      apply congrArg
      conv_rhs => rw [←sum_fibers_eq tag (fun i=>‖w i‖^2)]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr (by ext j; simp)
      intro j _
      rfl

#print axioms character_block_gram
end WaringLinear
