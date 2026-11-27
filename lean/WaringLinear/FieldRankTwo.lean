import WaringLinear.RankTwoPacking
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.Matrix.Block

/-! The two number-field directions in a box supply all rational
directions after multiplication by a fixed rational basis of the field.
Archimedean multiplication by an arbitrary frequency only shears the
resulting lattice. The determinant below retains precisely the ratio of
the two volumes, for real and complex coordinates alike. -/
noncomputable section
open Module
namespace WaringLinear.LatticePacking

private def twoIndices (ι : Type*) : (ι × Fin 2) ≃ ι ⊕ ι where
  toFun p := if p.2=0 then Sum.inl p.1 else Sum.inr p.1
  invFun s := Sum.elim (fun i => (i,0)) (fun i => (i,1)) s
  left_inv p := by rcases p with ⟨i,j⟩; fin_cases j <;> rfl
  right_inv s := by cases s <;> rfl

/-- The real diagonal blocks record the two embeddings; the lower-left
matrix may be any real matrix, including a complex multiplication block. -/
def sheared {ι : Type*} (x y : ℝ) (a c b : Matrix ι ι ℝ) :
    Matrix (ι⊕ι) (ι⊕ι) ℝ := Matrix.fromBlocks (x • a) 0 (y • c) (y • b)

theorem sheared_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ℝ) (a c b : Matrix ι ι ℝ) :
    (sheared x y a c b).det = (x^Fintype.card ι*y^Fintype.card ι)*(a.det*b.det) := by
  simp only [sheared,Matrix.det_fromBlocks_zero₁₂,Matrix.det_smul]
  ring

/-- Rank two plus the integral-basis multiples inside the moderately
enlarged box gives the full-volume bound. In the local application
x = T^(-1/n) and y = Y^(1/n). -/
theorem rank_two_count {ι K E : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    [Algebra ℚ K] [AddCommGroup E] [Module K E] [Module ℚ E] [IsScalarTower ℚ K E]
    (bK : Basis ι ℚ K) (v : Basis (Fin 2) K E) (b₀ : Basis (ι⊕ι) ℚ E)
    (small large : Finset E) (hsub : small ⊆ large)
    (hlattice : ∀ x∈large, x∈lattice b₀)
    (hfull : ∀ i j, bK i • v j ∈ large)
    (x y T Y : ℝ) (hx : x^Fintype.card ι=1/T) (hy : y^Fintype.card ι=Y)
    (hT : 0<T) (hY : 0<Y)
    (a c b : Matrix ι ι ℝ)
    (hbox : ∀ z∈large, ∀i, |∑j, sheared x y a c b i j * (b₀.repr z j : ℝ)| ≤ 1) :
    (small.card:ℝ) * |a.det * b.det| * Y ≤
      (Nat.factorial (2*Fintype.card ι):ℝ)*3^(2*Fintype.card ι)*T := by
  classical
  let basis := (bK.smulTower v).reindex (twoIndices ι)
  have hmem (j : ι⊕ι) : basis j∈large := by
    simp only [basis, Basis.reindex_apply, Basis.smulTower_apply]
    exact hfull _ _
  have h := card_mul_covolume_le b₀ large hlattice ⟨basis,hmem⟩ (sheared x y a c b) hbox
  rw [sheared_det,hx,hy,abs_mul,abs_mul,abs_of_pos (by positivity : (0:ℝ)<1/T),
    abs_of_pos hY,Fintype.card_sum] at h
  rw [←two_mul] at h
  have hcard : (small.card:ℝ) ≤ large.card := by exact_mod_cast Finset.card_le_card hsub
  calc
    _ ≤ (large.card:ℝ) * |a.det * b.det| * Y := by gcongr
    _ = (large.card*((1/T*Y)*|a.det*b.det|))*T := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right h hT.le

#print axioms rank_two_count
end WaringLinear.LatticePacking
