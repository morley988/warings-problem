import WaringLinear.IdealGram
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Factorization.Induction

/-! # An explicit root multiplicity bound for odd scalar moduli -/
noncomputable section
open scoped BigOperators Classical
namespace WaringLinear

theorem unitRootsCount_prod (A B : Type*) [Monoid A] [Monoid B] (k : ℕ) :
    unitRootsCount (A×B) k=unitRootsCount A k*unitRootsCount B k := by
  let f : (A×B)ˣ≃*Aˣ×Bˣ := MulEquiv.prodUnits
  let e : {u:(A×B)ˣ // u^k=1}≃{v:Aˣ×Bˣ // v.1^k=1 ∧ v.2^k=1} :=
    f.toEquiv.subtypeEquiv (fun u => by
      change u^k=1 ↔ (f u).1^k=1 ∧ (f u).2^k=1
      rw [←f.injective.eq_iff,map_pow,map_one]
      exact Prod.ext_iff)
  let v := Equiv.subtypeProdEquivProd (p:=fun u:Aˣ => u^k=1) (q:=fun u:Bˣ => u^k=1)
  exact (Nat.card_congr (e.trans v)).trans (Nat.card_prod _ _)

/-- Each component of odd prime-power conductor has cyclic unit group.
The estimate holds even at primes dividing the degree. -/
theorem odd_unitRootsCount (q k : ℕ) (hq : q≠0) (hq2 : ¬2∣q) (hk : 0<k) :
    unitRootsCount (ZMod q) k≤k^q.primeFactors.card := by
  induction q using Nat.recOnPrimePow with
  | zero => contradiction
  | one =>
    have h : Subsingleton {u:(ZMod 1)ˣ // u^k=1} := inferInstance
    rw [unitRootsCount,Nat.card_eq_fintype_card]
    simpa using (Fintype.card_le_one_iff_subsingleton.mpr h)
  | prime_pow_mul a p n hp hpa hn ih =>
    have ha : a≠0 := right_ne_zero_of_mul hq
    have h2a : ¬2∣a := fun h => hq2 (h.trans (dvd_mul_left ..))
    have hp2 : p≠2 := by
      intro he
      subst p
      exact hq2 ((dvd_pow_self 2 hn.ne').trans (dvd_mul_right ..))
    letI : NeZero (p^n) := ⟨pow_ne_zero _ hp.ne_zero⟩
    letI : IsCyclic (ZMod (p^n))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 n
    have hcyc : unitRootsCount (ZMod (p^n)) k≤k := by
      rw [unitRootsCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
      exact IsCyclic.card_pow_eq_one_le hk
    have cop : (p^n).Coprime a := (hp.coprime_iff_not_dvd.mpr hpa).pow_left n
    rw [unitRootsCount_congr (ZMod.chineseRemainder cop).toMulEquiv,unitRootsCount_prod,
      Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) ha,
      Finset.card_union_of_disjoint cop.disjoint_primeFactors,
      Nat.primeFactors_pow _ hn.ne',hp.primeFactors,Finset.card_singleton,pow_add,pow_one]
    exact Nat.mul_le_mul hcyc (ih ha h2a)

/-- A residue class is occupied at most floor(B/d)+1 times by any
subset of the integers in [0,B]. -/
theorem scalar_residue_occupancy (s : Finset ℕ) (B d : ℕ)
    (hB : ∀n∈s,n≤B) (r:ZMod d) :
    Nat.card {n:s // (n.val:ZMod d)=r} ≤ B/d+1 := by
  let f (n : {n:s // (n.val:ZMod d)=r}) : Fin (B/d+1) :=
    ⟨n.val.val/d,Nat.lt_succ_of_le (Nat.div_le_div_right (hB _ n.val.property))⟩
  have hf : Function.Injective f := by
    intro x y h
    have hdiv := congrArg Fin.val h
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp (x.property.trans y.property.symm)
    apply Subtype.ext
    apply Subtype.ext
    change x.val.val/d=y.val.val/d at hdiv
    calc
      x.val.val = x.val.val%d+d*(x.val.val/d) := (Nat.mod_add_div ..).symm
      _ = y.val.val%d+d*(y.val.val/d) := by rw [hmod,hdiv]
      _ = _ := Nat.mod_add_div .. 
  simpa using Nat.card_le_card_of_injective f hf

/-- Exact occupancy input for the small-denominator Gram on a coprime box:
at most (floor(B/d)+1) k^ω(d) roots above each residue. -/
theorem scalar_power_occupancy (s : Finset ℕ) (B d k : ℕ) [NeZero d]
    (hB : ∀n∈s,n≤B) (hgood : ∀n∈s,IsUnit (n:ZMod d))
    (hd : ¬2∣d) (hk : 0<k) (r : ZMod d) :
    Nat.card {n:s // (n.val:ZMod d)^k=r} ≤ (B/d+1)*k^d.primeFactors.card := by
  classical
  let f (n:s) : (ZMod d)ˣ := (hgood n.val n.property).unit
  let g (u:(ZMod d)ˣ) := (u:ZMod d)^k
  have hf (u:(ZMod d)ˣ) : Nat.card {x:s // f x = u} ≤ B/d+1 := by
    let h : {x:s // f x = u}→{x:s // (x.val:ZMod d)=u.val} := fun x =>
      ⟨x.val,by simpa [f] using congrArg Units.val x.property⟩
    exact (Nat.card_le_card_of_injective h (by intro x y hh; exact Subtype.ext (congrArg (fun u:{x:s // (x.val:ZMod d)=u.val} => u.val) hh))).trans
      (scalar_residue_occupancy s B d hB u.val)
  have hN := count_composite_fibre f g r (B/d+1) (k^d.primeFactors.card) hf
    ((unit_power_fibre_le (ZMod d) k r).trans (odd_unitRootsCount _ _ (NeZero.ne _) hd hk))
  simpa [g,f] using hN

#print axioms odd_unitRootsCount
#print axioms scalar_power_occupancy
end WaringLinear
