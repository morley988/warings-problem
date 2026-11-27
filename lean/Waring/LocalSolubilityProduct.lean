import Waring.LocalSolubilityWaring
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient

/-! # Positive local counts for product-box variables

Every ordinary solution lifts to many product-variable solutions: all but
one factor in each product may be chosen arbitrarily among the units.
The construction is injective and works at every nonzero modulus.
-/

noncomputable section
open scoped BigOperators
namespace Waring.LocalSolubility

/-- `L+1` factors per product variable; `u` ordinary and `v` product variables. -/
def productPowerSolutions (k u v L q : ℕ) [NeZero q] (n : ℤ) :
    Finset ((Fin u → ZMod q) × (Fin v → Fin (L+1) → ZMod q)) :=
  Finset.univ.filter (fun z => (∑ i,(z.1 i)^k)+
    (∑ j,(∏ l,z.2 j l)^k)=(n : ZMod q))

def unitProductLift {q L : ℕ} (a : ZMod q) (w : Fin L → (ZMod q)ˣ) :
    Fin (L+1) → ZMod q :=
  Fin.cons (a*↑((∏ l,w l)⁻¹)) (fun l => ↑(w l))

theorem unitProductLift_product {q L : ℕ} (a : ZMod q) (w : Fin L → (ZMod q)ˣ) :
    (∏ l,unitProductLift a w l)=a := by
  simp only [unitProductLift,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  rw [← Units.coe_prod, mul_assoc,Units.inv_mul]
  exact mul_one a

theorem unitProductLift_injective {q L : ℕ} :
    Function.Injective (fun z : ZMod q × (Fin L → (ZMod q)ˣ) => unitProductLift z.1 z.2) := by
  rintro ⟨a,w⟩ ⟨b,z⟩ h
  apply Prod.ext
  · have he := congrArg (fun f : Fin (L+1) → ZMod q => ∏ l,f l) h
    simpa only [unitProductLift_product] using he
  · funext l
    apply Units.ext
    exact congrFun h l.succ

def liftPowerSolution {u v L q : ℕ} (x : Fin (u+v) → ZMod q)
    (w : Fin v → Fin L → (ZMod q)ˣ) :
    (Fin u → ZMod q) × (Fin v → Fin (L+1) → ZMod q) :=
  (fun i => x (Fin.castAdd v i),fun j => unitProductLift (x (Fin.natAdd u j)) (w j))

theorem liftPowerSolution_mem {k u v L q : ℕ} [NeZero q] {n : ℤ}
    {x : Fin (u+v) → ZMod q} (hx : x ∈ powerSolutions k (u+v) q n)
    (w : Fin v → Fin L → (ZMod q)ˣ) :
    liftPowerSolution x w ∈ productPowerSolutions k u v L q n := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  simp only [liftPowerSolution,unitProductLift_product]
  have he := (Finset.mem_filter.mp hx).2
  rw [Fin.sum_univ_add] at he
  exact he

theorem liftPowerSolution_injective {u v L q : ℕ} :
    Function.Injective (fun z : (Fin (u+v) → ZMod q) × (Fin v → Fin L → (ZMod q)ˣ) =>
      liftPowerSolution z.1 z.2) := by
  rintro ⟨x,w⟩ ⟨y,z⟩ h
  have hfirst := congrArg Prod.fst h
  have hsecond := congrArg Prod.snd h
  have htail (j : Fin v) : x (Fin.natAdd u j)=y (Fin.natAdd u j) ∧ w j=z j := by
    have he := unitProductLift_injective (a₁ := (x (Fin.natAdd u j),w j))
      (a₂ := (y (Fin.natAdd u j),z j)) (congrFun hsecond j)
    exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
  apply Prod.ext
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact congrFun hfirst j
    · exact (htail j).1
  · funext j
    exact (htail j).2

/-- The multiplicity factor is exact and has all `(L*v)` unit choices. -/
theorem productPowerSolutions_card_lower (k u v L q : ℕ) [NeZero q] (n : ℤ) :
    (powerSolutions k (u+v) q n).card*(Nat.totient q)^(L*v) ≤
      (productPowerSolutions k u v L q n).card := by
  have hh := Finset.card_le_card_of_injOn
    (fun z : (Fin (u+v) → ZMod q) × (Fin v → Fin L → (ZMod q)ˣ) => liftPowerSolution z.1 z.2)
    (s := (powerSolutions k (u+v) q n).product Finset.univ)
    (t := productPowerSolutions k u v L q n)
    (by intro z hz; exact liftPowerSolution_mem (Finset.mem_product.mp hz).1 z.2)
    (fun _ _ _ _ h => liftPowerSolution_injective h)
  calc
    _ = ((powerSolutions k (u+v) q n).product
        (Finset.univ : Finset (Fin v → Fin L → (ZMod q)ˣ))).card := by
      have hc := Finset.card_product (powerSolutions k (u+v) q n)
        (Finset.univ : Finset (Fin v → Fin L → (ZMod q)ˣ))
      change ((powerSolutions k (u+v) q n).product
        (Finset.univ : Finset (Fin v → Fin L → (ZMod q)ˣ))).card = _ at hc
      rw [hc,Finset.card_univ]
      simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card_units_eq_totient,← pow_mul]
    _ ≤ _ := hh

theorem degree8_product_local_count_lower {p : ℕ} [NeZero p] (hp : p.Prime)
    (L r : ℕ) (n : ℤ) :
    p^(37*r)*(Nat.totient (p^(r+localDepth8 p)))^(L*30) ≤
      (productPowerSolutions 8 8 30 L (p^(r+localDepth8 p)) n).card := by
  exact (Nat.mul_le_mul_right _ (degree8_local_count_lower hp r n)).trans
    (productPowerSolutions_card_lower 8 8 30 L _ n)

theorem degree9_product_local_count_lower {p : ℕ} [NeZero p] (hp : p.Prime)
    (L r : ℕ) (n : ℤ) :
    p^(45*r)*(Nat.totient (p^(r+localDepth9 p)))^(L*35) ≤
      (productPowerSolutions 9 11 35 L (p^(r+localDepth9 p)) n).card := by
  exact (Nat.mul_le_mul_right _ (degree9_local_count_lower hp r n)).trans
    (productPowerSolutions_card_lower 9 11 35 L _ n)

#print axioms productPowerSolutions_card_lower
#print axioms degree8_product_local_count_lower
#print axioms degree9_product_local_count_lower
end Waring.LocalSolubility
