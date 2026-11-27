import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Real.Basic

/-! # A finite-box bound for a full-rank lattice

Choose a tuple in the finite set maximizing the determinant. Every point
has coordinates of absolute value at most one in this tuple. The coset
in the lattice quotient and the floors of its coordinates determine the
point, giving at most three to the dimension times the largest index.
-/
noncomputable section
open Module Function Set
namespace WaringLinear.LatticePacking
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup E] [Module ℚ E]

def lattice (b : Basis ι ℚ E) : AddSubgroup E :=
  .closure (Set.range b)

omit [Fintype ι] in
private theorem coordinate_integer (b : Basis ι ℚ E) {x : E}
    (hx : x ∈ lattice b) (i : ι) : ∃ z : ℤ, b.repr x i = z := by
  change x ∈ AddSubgroup.closure (Set.range b) at hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    classical
    by_cases hij : j=i
    · subst j
      exact ⟨1,by simp⟩
    · exact ⟨0,by simp [hij]⟩
  | zero => exact ⟨0,by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a,ha⟩ := hx
    obtain ⟨c,hc⟩ := hy
    exact ⟨a+c,by simp [ha,hc]⟩
  | neg x _ hx =>
    obtain ⟨a,ha⟩ := hx
    exact ⟨-a,by simp [ha]⟩

private def floorCode (x : ℚ) (h : |x|≤1) : Fin 3 :=
  ⟨(⌊x⌋+1).toNat,by
    have hh : ⌊x⌋≤1 := (Int.floor_le_iff).2 (by
      have := (abs_le.mp h).2
      norm_num at *
      linarith)
    omega⟩

private theorem floorCode_same {x y : ℚ} {hx : |x|≤1} {hy : |y|≤1}
    (h : floorCode x hx=floorCode y hy) : ⌊x⌋=⌊y⌋ := by
  have hx' : (-1:ℤ)≤⌊x⌋ := Int.le_floor.mpr (by simpa using (abs_le.mp hx).1)
  have hy' : (-1:ℤ)≤⌊y⌋ := Int.le_floor.mpr (by simpa using (abs_le.mp hy).1)
  have h' := congrArg Fin.val h
  change (⌊x⌋+1).toNat = (⌊y⌋+1).toNat at h'
  omega

/-- Bounded coordinates and the lattice index give a sharp-volume bound
up to a dimension constant. -/
theorem card_le_index (b b₀ : Basis ι ℚ E) (s : Finset E)
    (hincl : lattice b ≤ lattice b₀) (hs : ∀x∈s, x∈lattice b₀)
    (hcoord : ∀x∈s, ∀i, |b.repr x i|≤1) :
    (s.card : ℚ) ≤ |b₀.det b| * 3^Fintype.card ι := by
  classical
  let L := lattice b₀
  let H := (lattice b).addSubgroupOf L
  have hindex : (((lattice b).relIndex L : ℕ):ℚ) = |b₀.det b| :=
    AddSubgroup.relIndex_eq_abs_det _ _ hincl b b₀ rfl rfl
  have hn : Nat.card (L ⧸ H) ≠ 0 := by
    have hne := (b₀.isUnit_det b).ne_zero
    intro he
    change (lattice b).relIndex L=0 at he
    rw [he] at hindex
    simpa using (abs_pos.mpr hne).ne' hindex.symm
  letI : Finite (L ⧸ H) := Nat.finite_of_card_ne_zero hn
  let enc (x : s) : (L ⧸ H) × (ι → Fin 3) :=
    (QuotientAddGroup.mk (⟨x.val, hs _ x.property⟩ : L),
     fun i => floorCode (b.repr x.val i) (hcoord _ x.property i))
  have inj : Injective enc := by
    intro x y h
    have hc := congrArg Prod.fst h
    have hd := congrArg Prod.snd h
    have hmem : x.val-y.val ∈ lattice b := by
      change ((⟨x.val, hs _ x.property⟩ : L) : L⧸H)=
        ((⟨y.val, hs _ y.property⟩ : L) : L⧸H) at hc
      have hh : (⟨x.val,hs _ x.property⟩:L) - ⟨y.val,hs _ y.property⟩ ∈ H :=
        QuotientAddGroup.eq_iff_sub_mem.mp hc
      exact hh
    apply Subtype.ext
    apply b.repr.injective
    ext i
    obtain ⟨z,hz⟩ := coordinate_integer b hmem i
    rw [map_sub,Finsupp.sub_apply] at hz
    have hxy : b.repr x.val i = b.repr y.val i + z := by linarith
    have hf := floorCode_same (hx := hcoord _ x.property i)
      (hy := hcoord _ y.property i) (congrFun hd i)
    rw [hxy,Int.floor_add_intCast] at hf
    have hz' : z=0 := by omega
    simp [hxy,hz']
  have hh := Nat.card_le_card_of_injective enc inj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := (ι → Fin 3)),
    Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card (α := s),
    Fintype.card_coe] at hh
  have hcast : (s.card:ℚ) ≤ ((Nat.card (L⧸H):ℕ):ℚ)*3^Fintype.card ι := by
    exact_mod_cast hh
  exact hcast.trans_eq (by rw [←hindex]; rfl)

/-- Select a determinant-maximizing basis inside the box. -/
theorem card_le_max_det (b₀ : Basis ι ℚ E) (s : Finset E)
    (hs : ∀x∈s, x∈lattice b₀)
    (full : ∃ c : Basis ι ℚ E, ∀i, c i∈s) :
    ∃ v : ι → E, (∀i, v i∈s) ∧
      (s.card : ℚ) ≤ |b₀.det v| * 3^Fintype.card ι := by
  classical
  obtain ⟨c,hc⟩ := full
  let ⟨f,_,hm⟩ := Finset.exists_max_image
    (Finset.univ : Finset (ι → s)) (fun g => |b₀.det (fun i => (g i).val)|)
    ⟨fun i => ⟨c i,hc i⟩,Finset.mem_univ _⟩
  let v : ι → E := fun i => (f i).val
  have hmax (g : ι → E) (hg : ∀i, g i∈s) : |b₀.det g|≤|b₀.det v| :=
    hm (fun i => ⟨g i,hg i⟩) (Finset.mem_univ _)
  have hvpos : 0 < |b₀.det v| :=
    (abs_pos.mpr (b₀.isUnit_det c).ne_zero).trans_le (hmax c hc)
  have basis : LinearIndependent ℚ v ∧ Submodule.span ℚ (Set.range v)=⊤ :=
    b₀.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr (abs_pos.mp hvpos))
  let b := Basis.mk basis.1 basis.2.ge
  have hb : ⇑b=v := Basis.coe_mk _ _
  have incl : lattice b ≤ lattice b₀ := by
    change AddSubgroup.closure (Set.range b) ≤ lattice b₀
    apply (AddSubgroup.closure_le (lattice b₀)).2
    rintro x ⟨i,rfl⟩
    rw [hb]
    exact hs _ (f i).property
  refine ⟨v,fun i => (f i).property,?_⟩
  rw [← hb]
  apply card_le_index b b₀ s incl hs
  intro x hx i
  have hbox : ∀ j, Function.update v i x j ∈ s := by
    intro j
    by_cases hj : j=i
    · subst j
      rw [Function.update_self]
      exact hx
    · rw [Function.update_of_ne hj]
      exact (f j).property
  have hdet := hmax _ hbox
  have hc' := LinearMap.congr_fun
    (b₀.det_smul_mk_coord_eq_det_update basis.1 basis.2.ge i) x
  change b₀.det v * (b.repr x i) = b₀.det (Function.update v i x) at hc'
  rw [←hc',abs_mul] at hdet
  exact (le_of_mul_le_mul_left (by simpa using hdet) hvpos)

/-- In real coordinates, a linear transformation of the integer lattice
whose rows put all points in a box of radius one gives a count inversely
proportional to its covolume. -/
theorem card_mul_covolume_le (b₀ : Basis ι ℚ E) (s : Finset E)
    (hs : ∀x∈s, x∈lattice b₀)
    (full : ∃ c : Basis ι ℚ E, ∀i, c i∈s)
    (A : Matrix ι ι ℝ)
    (hbox : ∀x∈s, ∀i, |∑j, A i j * (b₀.repr x j : ℝ)| ≤ 1) :
    (s.card : ℝ)*|A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ)*3^Fintype.card ι := by
  classical
  obtain ⟨v,hv,hcard⟩ := card_le_max_det b₀ s hs full
  let M : Matrix ι ι ℝ := (b₀.toMatrix v).map (Rat.castHom ℝ)
  have hd : |(A*M).det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) := by
    have hcell (i j : ι) : (AbsoluteValue.abs : AbsoluteValue ℝ ℝ) ((A*M) i j) ≤ 1 := by
      simpa [M,Matrix.mul_apply,Basis.toMatrix_apply] using hbox (v j) (hv j) i
    simpa using Matrix.det_le hcell
  have hM : M.det = ((b₀.det v : ℚ) : ℝ) := by
    change ((Rat.castHom ℝ).mapMatrix (b₀.toMatrix v)).det = _
    rw [←RingHom.map_det]
    rfl
  rw [Matrix.det_mul, hM, abs_mul] at hd
  have hc : (s.card:ℝ) ≤ |((b₀.det v:ℚ):ℝ)| * 3^Fintype.card ι := by
    exact_mod_cast hcard
  calc
    _ ≤ (|((b₀.det v:ℚ):ℝ)| * 3^Fintype.card ι)*|A.det| :=
       mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ = (|A.det| * |((b₀.det v:ℚ):ℝ)|)*3^Fintype.card ι := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (by positivity)

#print axioms card_le_max_det
#print axioms card_mul_covolume_le
end WaringLinear.LatticePacking
