import WaringLinear.CharacterBlocks
import WaringLinear.ScalarConductorGram
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # Actual mod-d Fourier blocks on the rational circle -/
noncomputable section
open scoped BigOperators Classical ComplexConjugate
namespace WaringLinear

private theorem torsion_has_index (d : ℕ) [NeZero d] (u : ScalarTorus) (h : d • u=0) :
    ∃r:ZMod d,ZMod.toAddCircle r=u := by
  obtain ⟨j,_,hj⟩ := (AddCircle.nsmul_eq_zero_iff (NeZero.pos d)).mp h
  exact ⟨j,by simpa [ZMod.toAddCircle_natCast] using hj⟩

private theorem std_phase (d : ℕ) [NeZero d] (r:ZMod d) (m:ℕ) :
    ZMod.stdAddChar (r*(m:ZMod d))=fourier (m:ℤ) (ZMod.toAddCircle r) := by
  change ((ZMod.toAddCircle (r*(m:ZMod d))).toCircle:ℂ)=_
  rw [mul_comm,←nsmul_eq_mul,map_nsmul,fourier_apply,natCast_zsmul]

private theorem conj_phase_product (n k:ℕ) (u a b:ScalarTorus) :
    conj (fourier ((n^k:ℕ):ℤ) (u-a))*fourier ((n^k:ℕ):ℤ) (u-b)=
          fourier ((n^k:ℕ):ℤ) (a-b) := by
  let m : ℤ := (n^k:ℕ)
  have hc (x : ScalarTorus) : conj (fourier m x)=fourier m (-x) := by
    symm
    rw [fourier_apply,smul_neg,←neg_smul,←fourier_apply,fourier_neg]
  have hadd (x y : ScalarTorus) : fourier m (x+y)=fourier m x*fourier m y := by
    simp only [fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul]
  change conj (fourier m (u-a))*fourier m (u-b)=fourier m (a-b)
  rw [hc,←hadd,show -(u-a)+(u-b)=a-b by abel]

/-- Actual small-conductor Gram operator for an arbitrary set of distinct
circle frequencies. Its only arithmetic input is an upper bound N for
the occupancy of any kth-power residue class modulo d. -/
theorem scalar_divisible_gram_bound
    {ι : Type*} [Fintype ι] (node : ι→ScalarTorus) (hnode : Function.Injective node)
    (box : Finset ℕ) (k d N : ℕ) [NeZero d]
    (hN : ∀r:ZMod d,Nat.card {x:box // (x.val:ZMod d)^k=r}≤N)
    (w : ι→ℂ) :
    ‖gramForm (fun a b:ι => if addOrderOf (node a-node b)∣d then
      scalarPowerSum box k (node a-node b) else 0) w‖ ≤
      ((N:ℝ)*d)*∑i,‖w i‖^2 := by
  classical
  let g (i:ι) := d • node i
  letI : Fintype (Set.range g) := (Set.finite_range g).fintype
  let tag (i:ι) : Set.range g := ⟨g i,i,rfl⟩
  let anchor (b:Set.range g) : ι := Classical.choose b.property
  have hA (b:Set.range g) : g (anchor b)=b.val := Classical.choose_spec b.property
  have tors (b:Set.range g) (i:{a // tag a=b}) : d • (node (anchor b)-node i.val)=0 := by
    rw [smul_sub]
    change g (anchor b)-g i.val=0
    rw [hA,show g i.val=b.val from congrArg Subtype.val i.property,sub_self]
  let code (b:Set.range g) (i:{a // tag a=b}) : ZMod d := Classical.choose
    (torsion_has_index d _ (tors b i))
  have hcode (b:Set.range g) (i:{a // tag a=b}) :
      ZMod.toAddCircle (code b i)=node (anchor b)-node i.val :=
    Classical.choose_spec (torsion_has_index d _ (tors b i))
  let χ (b:Set.range g) (i:{a // tag a=b}) : AddChar (ZMod d) ℂ := ZMod.stdAddChar.mulShift (code b i)
  have hinj (b:Set.range g) : Function.Injective (χ b) := by
    intro i j h
    have he : code b i=code b j := AddChar.to_mulShift_inj_of_isPrimitive (ZMod.isPrimitive_stdAddChar d) h
    have v := congrArg (ZMod.toAddCircle (N:=d)) he
    rw [hcode,hcode] at v
    exact Subtype.ext (hnode (sub_right_inj.mp v))
  let v (x:box) := (x.val:ZMod d)^k
  have hcor (b:Set.range g) (i j:{a // tag a=b}) :
      scalarPowerSum box k (node i.val-node j.val) =
      ∑x:box,conj (χ b i (v x))*χ b j (v x) := by
    unfold scalarPowerSum
    rw [←Finset.sum_coe_sort box (fun n => fourier ((n^k:ℕ):ℤ) (node i.val-node j.val))]
    apply Finset.sum_congr rfl
    intro x _
    simp only [χ, v, AddChar.mulShift_apply]
    rw [←Nat.cast_pow,std_phase,std_phase,hcode,hcode]
    exact (conj_phase_product ..).symm
  have H := character_block_gram tag v N hN χ hinj
    (fun a b=>scalarPowerSum box k (node a-node b)) hcor w
  have eq (a b:ι) : addOrderOf (node a-node b)∣d ↔ tag a=tag b := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero,smul_sub,sub_eq_zero]
    exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
  simp_rw [eq]
  simpa only [ZMod.card] using H

#print axioms scalar_divisible_gram_bound
end WaringLinear
