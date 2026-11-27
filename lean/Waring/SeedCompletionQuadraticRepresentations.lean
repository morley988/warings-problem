import Waring.SeedCompletionQuadraticRoots
import Mathlib.Data.Int.Order.Lemmas

/-!
# Positive representations by x^2 + 3 y^2

A primitive positive representation determines the root x/y modulo n.
Two representations with the same root have determinant divisible by n,
whereas the positive quadratic norm makes its absolute value smaller than
n. The primitive representations are therefore injected into the proved
quadratic root set. Splitting by the common divisor treats all pairs.
-/

noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionQuadraticRepresentations
open SeedCompletionQuadraticRoots

def representations (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => p.1^2+3*p.2^2=n)

def primitiveRepresentations (n : ℕ) : Finset (ℕ × ℕ) :=
  (representations n).filter (fun p => Nat.Coprime p.1 p.2)

@[simp] theorem mem_representations {n x y : ℕ} :
    (x,y) ∈ representations n ↔ 0 < x ∧ 0 < y ∧ x^2+3*y^2=n := by
  simp only [representations,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨by omega,by omega,h.2⟩
  · rintro ⟨hx,hy,hn⟩
    have hxle : x ≤ n := by nlinarith
    have hyle : y ≤ n := by nlinarith
    exact ⟨⟨⟨by omega,hxle⟩,⟨by omega,hyle⟩⟩,hn⟩

@[simp] theorem mem_primitiveRepresentations {n x y : ℕ} :
    (x,y) ∈ primitiveRepresentations n ↔
      0 < x ∧ 0 < y ∧ x^2+3*y^2=n ∧ Nat.Coprime x y := by
  simp [primitiveRepresentations,and_assoc]

theorem denominator_coprime {n x y : ℕ} (hn : x^2+3*y^2=n)
    (hxy : Nat.Coprime x y) : Nat.Coprime y n := by
  rw [← hn]
  have h := (Nat.coprime_add_mul_right_right y (x^2) (3*y)).mpr (hxy.symm.pow_right 2)
  convert h using 1 <;> ring

def representationRoot (n : ℕ) (p : ℕ × ℕ) : ℕ :=
  ((p.1 : ZMod n)*(p.2 : ZMod n)⁻¹).val

theorem representationRoot_mem {n x y : ℕ} (hn : 0 < n)
    (hp : (x,y) ∈ primitiveRepresentations n) :
    representationRoot n (x,y) ∈ quadraticRoots n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨hx,hy,heq,hcop⟩ := mem_primitiveRepresentations.mp hp
  have hunit : (y : ZMod n)*(y : ZMod n)⁻¹=1 :=
    ZMod.coe_mul_inv_eq_one y (denominator_coprime heq hcop)
  have hnorm : (x : ZMod n)^2+3*(y : ZMod n)^2=0 := by
    have h := congrArg (fun t : ℕ => (t : ZMod n)) heq
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,ZMod.natCast_self] using h
  have hroot : ((x : ZMod n)*(y : ZMod n)⁻¹)^2+3=0 := by
    have hs := congrArg (fun t : ZMod n => t^2) hunit
    linear_combination (y : ZMod n)⁻¹^2*hnorm - 3*hs
  apply mem_quadraticRoots.mpr
  refine ⟨ZMod.val_lt _,?_⟩
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [representationRoot,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,
    ZMod.natCast_zmod_val] using hroot

/-- The determinant of two norm-n vectors has absolute value strictly below
n, because the second coefficient is three and n is positive. -/
theorem determinant_eq_zero_of_dvd {n x y u v : ℕ} (hn : 0 < n)
    (hxy : x^2+3*y^2=n) (huv : u^2+3*v^2=n)
    (hd : (n : ℤ) ∣ (x : ℤ)*v-(u : ℤ)*y) : x*v=u*y := by
  have hxyZ : (x : ℤ)^2+3*(y : ℤ)^2=(n : ℤ) := by exact_mod_cast hxy
  have huvZ : (u : ℤ)^2+3*(v : ℤ)^2=(n : ℤ) := by exact_mod_cast huv
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hid : ((x : ℤ)*u+3*(y : ℤ)*v)^2+
      3*((x : ℤ)*v-(u : ℤ)*y)^2=(n : ℤ)^2 := by
    calc
      _ = ((x : ℤ)^2+3*(y : ℤ)^2)*((u : ℤ)^2+3*(v : ℤ)^2) := by ring
      _ = _ := by rw [hxyZ,huvZ]; ring
  have hlt : ((x : ℤ)*v-(u : ℤ)*y)^2 < (n : ℤ)^2 := by
    nlinarith [sq_nonneg ((x : ℤ)*u+3*(y : ℤ)*v)]
  have hz := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (Int.natAbs_lt_iff_mul_self_lt.mpr (by simpa only [pow_two] using hlt))
  exact_mod_cast sub_eq_zero.mp hz

/-- Primitive positive representations with the same modular root coincide. -/
theorem representationRoot_injOn {n : ℕ} (hn : 0 < n) :
    Set.InjOn (representationRoot n) (primitiveRepresentations n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  rintro ⟨x,y⟩ hxy ⟨u,v⟩ huv hr
  obtain ⟨hx,hy,hxyN,hxyCop⟩ := mem_primitiveRepresentations.mp hxy
  obtain ⟨hu,hv,huvN,huvCop⟩ := mem_primitiveRepresentations.mp huv
  have hyunit := ZMod.coe_mul_inv_eq_one y (denominator_coprime hxyN hxyCop)
  have hvunit := ZMod.coe_mul_inv_eq_one v (denominator_coprime huvN huvCop)
  have hroot : (x : ZMod n)*(y : ZMod n)⁻¹=(u : ZMod n)*(v : ZMod n)⁻¹ := by
    have h := congrArg (fun t : ℕ => (t : ZMod n)) hr
    simpa only [representationRoot,ZMod.natCast_zmod_val] using h
  have hcross : (x : ZMod n)*(v : ZMod n)=(u : ZMod n)*(y : ZMod n) := by
    calc
      _ = ((x : ZMod n)*(y : ZMod n)⁻¹)*((y : ZMod n)*(v : ZMod n)) := by
        calc
          _ = (x : ZMod n)*((y : ZMod n)*(y : ZMod n)⁻¹)*(v : ZMod n) := by rw [hyunit]; ring
          _ = _ := by ring
      _ = ((u : ZMod n)*(v : ZMod n)⁻¹)*((y : ZMod n)*(v : ZMod n)) := by rw [hroot]
      _ = (u : ZMod n)*((v : ZMod n)*(v : ZMod n)⁻¹)*(y : ZMod n) := by ring
      _ = _ := by rw [hvunit]; ring
  have hdiv : (n : ℤ) ∣ (x : ℤ)*v-(u : ℤ)*y := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
    push_cast
    exact sub_eq_zero.mpr hcross
  have heq := determinant_eq_zero_of_dvd hn hxyN huvN hdiv
  have hxdu : x ∣ u := hxyCop.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right x v)
  have hudx : u ∣ x := huvCop.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right u y)
  have hxu : x=u := Nat.dvd_antisymm hxdu hudx
  have hyv : y=v := by
    rw [← hxu] at heq
    exact (Nat.mul_left_cancel hx heq).symm
  exact Prod.ext hxu hyv

/-- The primitive representation bound is an actual finite injection. -/
theorem primitiveRepresentations_card_le_divisors_sq {n : ℕ} (hn : 0 < n) :
    (primitiveRepresentations n).card ≤ n.divisors.card^2 := by
  apply (Finset.card_le_card_of_injOn (representationRoot n) ?_ (representationRoot_injOn hn)).trans
    (quadraticRoots_card_le_divisors_sq hn)
  rintro ⟨x,y⟩ hp
  exact representationRoot_mem hn hp

/-- Dividing a representation by its common divisor gives an actual
primitive representation of the corresponding quotient norm. -/
theorem representation_reduction {n x y : ℕ} (hp : (x,y) ∈ representations n) :
    0 < Nat.gcd x y ∧ (Nat.gcd x y)^2 ∣ n ∧
      (x/Nat.gcd x y,y/Nat.gcd x y) ∈
        primitiveRepresentations (n/(Nat.gcd x y)^2) := by
  obtain ⟨hx,hy,hnorm⟩ := mem_representations.mp hp
  let g := Nat.gcd x y
  have hg : 0 < g := Nat.gcd_pos_of_pos_left y hx
  have hdx : g ∣ x := Nat.gcd_dvd_left x y
  have hdy : g ∣ y := Nat.gcd_dvd_right x y
  have hxm : g*(x/g)=x := Nat.mul_div_cancel' hdx
  have hym : g*(y/g)=y := Nat.mul_div_cancel' hdy
  have hnormmul : g^2*((x/g)^2+3*(y/g)^2)=n := by
    calc
      _ = (g*(x/g))^2+3*(g*(y/g))^2 := by ring
      _ = n := by rw [hxm,hym,hnorm]
  have hd : g^2 ∣ n := ⟨(x/g)^2+3*(y/g)^2,hnormmul.symm⟩
  have hxg : 0 < x/g := Nat.div_pos (Nat.le_of_dvd hx hdx) hg
  have hyg : 0 < y/g := Nat.div_pos (Nat.le_of_dvd hy hdy) hg
  have hn' : (x/g)^2+3*(y/g)^2=n/g^2 := by
    apply Nat.mul_left_cancel (pow_pos hg 2)
    rw [Nat.mul_div_cancel' hd]
    exact hnormmul
  exact ⟨hg,hd,mem_primitiveRepresentations.mpr
    ⟨hxg,hyg,hn',Nat.coprime_div_gcd_div_gcd hg⟩⟩

/-- At a fixed common divisor, division injects into the primitive pairs. -/
theorem fixed_gcd_injective (n g : ℕ) :
    Set.InjOn (fun p : ℕ × ℕ => (p.1/g,p.2/g))
      ((representations n).filter (fun p => Nat.gcd p.1 p.2=g)) := by
  intro x hx y hy heq
  have hxg := (Finset.mem_filter.mp hx).2
  have hyg := (Finset.mem_filter.mp hy).2
  have hxd1 : g ∣ x.1 := hxg ▸ Nat.gcd_dvd_left x.1 x.2
  have hxd2 : g ∣ x.2 := hxg ▸ Nat.gcd_dvd_right x.1 x.2
  have hyd1 : g ∣ y.1 := hyg ▸ Nat.gcd_dvd_left y.1 y.2
  have hyd2 : g ∣ y.2 := hyg ▸ Nat.gcd_dvd_right y.1 y.2
  apply Prod.ext
  · calc
      x.1 = g*(x.1/g) := (Nat.mul_div_cancel' hxd1).symm
      _ = g*(y.1/g) := congrArg (fun t : ℕ => g*t) (congrArg Prod.fst heq)
      _ = y.1 := Nat.mul_div_cancel' hyd1
  · calc
      x.2 = g*(x.2/g) := (Nat.mul_div_cancel' hxd2).symm
      _ = g*(y.2/g) := congrArg (fun t : ℕ => g*t) (congrArg Prod.snd heq)
      _ = y.2 := Nat.mul_div_cancel' hyd2

theorem fixed_gcd_card_le {n : ℕ} (hn : 0 < n) (g : ℕ) :
    ((representations n).filter (fun p => Nat.gcd p.1 p.2=g)).card ≤ n.divisors.card^2 := by
  classical
  by_cases he : ((representations n).filter (fun p => Nat.gcd p.1 p.2=g)).Nonempty
  · obtain ⟨x,hx⟩ := he
    have hred := representation_reduction (Finset.mem_filter.mp hx).1
    rw [(Finset.mem_filter.mp hx).2] at hred
    have hq : 0 < n/g^2 := Nat.div_pos (Nat.le_of_dvd hn hred.2.1) (pow_pos hred.1 2)
    have hqd : n/g^2 ∣ n := Nat.div_dvd_of_dvd hred.2.1
    have hcard : ((representations n).filter (fun p => Nat.gcd p.1 p.2=g)).card ≤
        (primitiveRepresentations (n/g^2)).card := by
      apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (p.1/g,p.2/g))
        _ (fixed_gcd_injective n g)
      intro y hy
      have H := (representation_reduction (Finset.mem_filter.mp hy).1).2.2
      simpa only [(Finset.mem_filter.mp hy).2] using H
    exact hcard.trans ((primitiveRepresentations_card_le_divisors_sq hq).trans
      (Nat.pow_le_pow_left (Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hqd)) 2))
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
    exact Nat.zero_le _

/-- A cubic divisor bound for every positive representation, including
nonprimitive pairs. There is no uniform quadratic-form theorem assumed. -/
theorem representations_card_le_divisors_cube {n : ℕ} (hn : 0 < n) :
    (representations n).card ≤ n.divisors.card^3 := by
  have hmap : Set.MapsTo (fun p : ℕ × ℕ => Nat.gcd p.1 p.2)
      (representations n) n.divisors := by
    intro x hx
    have hd := (representation_reduction hx).2.1
    exact Nat.mem_divisors.mpr ⟨(dvd_pow_self (Nat.gcd x.1 x.2) (by norm_num : 2 ≠ 0)).trans hd,hn.ne'⟩
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  calc
    _ ≤ ∑ _g ∈ n.divisors, n.divisors.card^2 :=
      Finset.sum_le_sum (fun g hg => fixed_gcd_card_le hn g)
    _ = n.divisors.card^3 := by simp [pow_succ,mul_comm]

/-- Every positive power loss is available with one uniform constant. -/
theorem representations_card_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      ((representations n).card : ℝ) ≤ C*(n : ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := AuxiliaryL2Grouping.divisor_power_le_rpow 3 hε
  refine ⟨C,hC,?_⟩
  intro n hn
  exact (show ((representations n).card : ℝ) ≤ (n.divisors.card : ℝ)^3 by
    exact_mod_cast representations_card_le_divisors_cube hn).trans (hdiv n hn)

#print axioms representations_card_le_rpow
#print axioms representationRoot_injOn
#print axioms primitiveRepresentations_card_le_divisors_sq
end Waring.SeedCompletionQuadraticRepresentations
