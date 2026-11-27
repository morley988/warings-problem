import WaringLinear.CubicDensities
import WaringLinear.CubicLocalLifting
import Mathlib.Algebra.QuadraticAlgebra
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic.NormNum

/-! # Three and four cubes in the ramified quadratic 3-adic order

For the explicit order ℤ₃[T]/(T²−6), representability is equivalent to
membership of its reduction modulo 9 in the previously computed sumset.
-/
namespace WaringLinear.RamifiedCubicOrder
open WaringLinear.CubicDensities
noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

abbrev Base := ℤ_[3]
abbrev Order := QuadraticAlgebra Base 6 0
private abbrev I : Ideal Order := Ideal.span {(3:Order)}
private abbrev J : Ideal Base := Ideal.span {(3:Base)}

private theorem scalar_pow_mul (n : ℕ) (x : Order) :
    (3:Order)^n*x =
      (⟨(3:Base)^n*x.re, (3:Base)^n*x.im⟩ : Order) := by
  have he : (3:Order)^n = algebraMap Base Order ((3:Base)^n) := by simp
  rw [he,QuadraticAlgebra.algebraMap_eq]
  ext <;> simp

private theorem mem_power (z : Order) (n : ℕ) :
    z ∈ I^n ↔ z.re ∈ J^n ∧ z.im ∈ J^n := by
  simp only [I,J,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x,rfl⟩
    rw [scalar_pow_mul]
    exact ⟨⟨x.re,rfl⟩,⟨x.im,rfl⟩⟩
  · rintro ⟨⟨x,hx⟩,⟨y,hy⟩⟩
    exact ⟨⟨x,y⟩, by rw [scalar_pow_mul]; exact QuadraticAlgebra.ext hx hy⟩

private instance baseComplete : IsAdicComplete J Base := by
  have he : IsLocalRing.maximalIdeal Base = J := by
    convert PadicInt.maximalIdeal_eq_span_p (p := 3) using 1
  rw [← he]
  infer_instance

private instance orderComplete : IsAdicComplete I Order where
  haus' x hx := by
    have hmem (n : ℕ) : x.re ∈ J^n ∧ x.im ∈ J^n := by
      apply (mem_power x n).mp
      simpa only [SModEq.sub_mem,sub_zero,Ideal.smul_eq_mul,Ideal.mul_top] using hx n
    apply QuadraticAlgebra.ext
    · apply IsHausdorff.haus' (I := J)
      intro n
      simpa only [SModEq.sub_mem,sub_zero,Ideal.smul_eq_mul,Ideal.mul_top] using (hmem n).1
    · apply IsHausdorff.haus' (I := J)
      intro n
      simpa only [SModEq.sub_mem,sub_zero,Ideal.smul_eq_mul,Ideal.mul_top] using (hmem n).2
  prec' f hf := by
    have hp {m n : ℕ} (hmn : m ≤ n) :
        (f m).re-(f n).re ∈ J^m ∧ (f m).im-(f n).im ∈ J^m := by
      have hmn' := hf hmn
      simp only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top] at hmn'
      exact (mem_power (f m-f n) m).mp hmn'
    obtain ⟨a,ha⟩ := IsPrecomplete.prec' (I := J) (fun n => (f n).re)
      (fun h => by simpa only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top] using (hp h).1)
    obtain ⟨b,hb⟩ := IsPrecomplete.prec' (I := J) (fun n => (f n).im)
      (fun h => by simpa only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top] using (hp h).2)
    refine ⟨⟨a,b⟩,fun n => ?_⟩
    simp only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top]
    apply (mem_power _ n).mpr
    simpa only [SModEq.sub_mem,Ideal.smul_eq_mul,Ideal.mul_top] using And.intro (ha n) (hb n)

private def red₁ : Base →+* ZMod 9 := PadicInt.toZModPow 2

/-- Coefficientwise reduction modulo 9 in the basis (1,T). -/
def reduce : Order →+ Residue where
  toFun x := (red₁ x.re,red₁ x.im)
  map_zero' := by simp
  map_add' x y := by ext <;> simp

theorem reduce_surjective : Function.Surjective reduce := by
  rintro ⟨x,y⟩
  refine ⟨⟨x.val,y.val⟩,?_⟩
  change (red₁ (x.val:Base),red₁ (y.val:Base)) = _
  simp

private theorem red₁_zero (x : Base) : red₁ x = 0 ↔ x ∈ J^2 := by
  change x ∈ RingHom.ker (PadicInt.toZModPow 2 : Base →+* ZMod (3^2)) ↔ _
  rw [PadicInt.ker_toZModPow]
  simp [J,Ideal.span_singleton_pow]

theorem reduce_zero (x : Order) : reduce x = 0 ↔ ∃ b : Order, x = 9*b := by
  change (red₁ x.re, red₁ x.im) = ((0,0):Residue) ↔ _
  rw [Prod.mk.injEq,red₁_zero,red₁_zero,← mem_power,Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  norm_num
  rfl

theorem reduce_cube (x : Order) : reduce (x^3) = cube (reduce x) := by
  have h₆ : red₁ (6:Base) = (6:ZMod 9) := by
    convert (map_natCast red₁ 6) using 1
  ext <;> simp [reduce,cube,pow_succ,h₆] <;> ring

/-- The inductive definition records exactly one new cube at each step. -/
def Represented : ℕ → Order → Prop
  | 0, n => n = 0
  | s+1, n => ∃ m x : Order, Represented s m ∧ m+x^3 = n

theorem reduced_representation {s : ℕ} {n : Order} (hn : Represented s n) :
    reduce n ∈ sums s := by
  induction s generalizing n with
  | zero => change n=0 at hn; simp [hn,sums]
  | succ s ih =>
    obtain ⟨m,x,hm,rfl⟩ := hn
    exact (mem_sums_succ _ _).mpr ⟨reduce m,ih hm,reduce x,by simp [reduce_cube]⟩

private theorem lift_residue_sum {s : ℕ} {z : Residue} (hz : z ∈ sums s) :
    ∃ n : Order, Represented s n ∧ reduce n = z := by
  induction s generalizing z with
  | zero =>
    have h : z=0 := by simpa [sums] using hz
    exact ⟨0,rfl,by simp [h]⟩
  | succ s ih =>
    obtain ⟨v,hv,y,rfl⟩ := (mem_sums_succ _ _).mp hz
    obtain ⟨m,hm,rfl⟩ := ih hv
    obtain ⟨x,rfl⟩ := reduce_surjective y
    exact ⟨m+x^3,⟨m,x,hm,rfl⟩,by simp [reduce_cube]⟩

private theorem lift_with_unit {s : ℕ} {n : Order} (hn : reduce n ∈ withUnit s) :
    Represented (s+1) n := by
  obtain ⟨⟨v,c⟩,hp,he⟩ := Finset.mem_image.mp hn
  obtain ⟨hv,hc⟩ := Finset.mem_product.mp hp
  obtain ⟨m,hm,hred⟩ := lift_residue_sum hv
  have hunit : ∃ u : Orderˣ, reduce ((u:Order)^3)=c := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · refine ⟨1, ?_⟩
      rw [Units.val_one,one_pow]
      change (red₁ 1,red₁ 0) = ((1,0):Residue)
      simp
    · refine ⟨-1,?_⟩
      rw [show ((↑(-1:Orderˣ):Order)^3) = -1 by simp; ring]
      change (red₁ (-1),red₁ 0) = _
      exact Prod.ext (by rw [map_neg,map_one]; decide) (by simp)
  obtain ⟨u,hu⟩ := hunit
  have he' : v+c=reduce n := he
  have hzero : reduce (n-m-(u:Order)^3)=0 := by simp [hred,hu,← he']
  obtain ⟨b,hb⟩ := (reduce_zero _).mp hzero
  obtain ⟨h,hh⟩ := CubicLocalLifting.unit_cube_coset I
    (Ideal.subset_span (Set.mem_singleton (3:Order))) u b
  refine ⟨m,(u:Order)+3*h,hm,?_⟩
  rw [hh,← hb]
  ring

theorem three_iff (n : Order) : Represented 3 n ↔ reduce n ∈ sums 3 :=
  ⟨reduced_representation,fun h => lift_with_unit (three_with_unit.symm ▸ h)⟩

theorem four_iff (n : Order) : Represented 4 n ↔ reduce n ∈ sums 4 :=
  ⟨reduced_representation,fun h => lift_with_unit (four_with_unit.symm ▸ h)⟩

set_option maxRecDepth 20000 in
private theorem five_with_unit : withUnit 4 = eligible := by decide

theorem five_iff (n : Order) : Represented 5 n ↔ reduce n ∈ eligible := by
  constructor
  · intro hn
    rw [← five_exact]
    exact reduced_representation hn
  · intro hn
    exact lift_with_unit (five_with_unit.symm ▸ hn)

private theorem represented_in_cube_span {s : ℕ} {n : Order} (hn : Represented s n) :
    n ∈ AddSubgroup.closure (Set.range fun x : Order => x^3) := by
  induction s generalizing n with
  | zero => change n=0 at hn; rw [hn]; exact AddSubgroup.zero_mem _
  | succ s ih =>
    obtain ⟨m,x,hm,rfl⟩ := hn
    exact AddSubgroup.add_mem _ (ih hm) (AddSubgroup.subset_closure ⟨x,rfl⟩)

private def small (x : ZMod 9) : Prop := x=0 ∨ x=3 ∨ x=6
private instance (x : ZMod 9) : Decidable (small x) := by unfold small; infer_instance
private theorem mem_eligible (x : Residue) : x ∈ eligible ↔ small x.2 := by
  simp [eligible,small]

private theorem eligible_closed :
    (∀ x : Residue, cube x ∈ eligible) ∧ (0 ∈ eligible) ∧
    (∀ x ∈ eligible, ∀ y ∈ eligible, x+y ∈ eligible) ∧
    (∀ x ∈ eligible, -x ∈ eligible) := by
  have hc : ∀ x : Residue, small (cube x).2 := by decide
  have ha : ∀ x y : ZMod 9, small x → small y → small (x+y) := by decide
  have hn : ∀ x : ZMod 9, small x → small (-x) := by decide
  simp only [mem_eligible]
  exact ⟨hc,by decide,fun x hx y hy => ha _ _ hx hy,fun x hx => hn _ hx⟩

theorem cube_span_iff (n : Order) :
    n ∈ AddSubgroup.closure (Set.range fun x : Order => x^3) ↔
    reduce n ∈ eligible := by
  constructor
  · intro hn
    induction hn using AddSubgroup.closure_induction with
    | mem _ h =>
      obtain ⟨z,rfl⟩ := h
      rw [reduce_cube]
      exact eligible_closed.1 _
    | zero => simpa using eligible_closed.2.1
    | add z t _ _ hz ht =>
      rw [map_add]
      exact eligible_closed.2.2.1 _ hz _ ht
    | neg _ _ hz =>
      rw [map_neg]
      exact eligible_closed.2.2.2 _ hz
  · exact fun h => represented_in_cube_span ((five_iff n).mpr h)

/-- Classes modulo 9 containing actual sums of a specified number of cubes. -/
def realizedClasses (s : ℕ) : Finset Residue := by
  classical
  exact Finset.univ.filter (fun r => ∃ n : Order, Represented s n ∧ reduce n = r)

private theorem realized_eq {s : ℕ} {T : Finset Residue}
    (h : ∀ n : Order, Represented s n ↔ reduce n ∈ T) : realizedClasses s = T := by
  classical
  ext r
  simp only [realizedClasses,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨n,hn,rfl⟩
    exact (h n).mp hn
  · intro hr
    obtain ⟨n,rfl⟩ := reduce_surjective r
    exact ⟨n,(h n).mpr hr,rfl⟩

/-- Exact numbers of residue classes attained by actual integral-adic
three-, four- and five-cube sums in the quadratic order. -/
theorem actual_class_counts :
    (realizedClasses 3).card = 17 ∧ (realizedClasses 4).card = 23 ∧
    (realizedClasses 5).card = 27 := by
  rw [realized_eq three_iff,realized_eq four_iff,realized_eq five_iff]
  exact ⟨three_card,four_card,eligible_card⟩

#print axioms cube_span_iff
#print axioms actual_class_counts
#print axioms three_iff
#print axioms four_iff
end
end WaringLinear.RamifiedCubicOrder
