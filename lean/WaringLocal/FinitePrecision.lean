import WaringLinear.CubicLocalLifting
import Mathlib.Tactic

/-! Equality of ordinary and primitive local Waring widths once the
nonunit powers lie strictly deeper than the unit-power precision. -/
namespace WaringLocal.FinitePrecision
variable {R : Type*} [CommRing R]

def Eligible (k : Nat) : AddSubgroup R :=
  AddSubgroup.closure (Set.range fun x : R => x^k)

def powerSum (k : Nat) (xs : List R) : R := (xs.map (·^k)).sum

def Ordinary (k s : Nat) (z : R) : Prop :=
  ∃ xs : List R, xs.length≤s ∧ powerSum k xs=z

def Primitive (k s : Nat) (z : R) : Prop :=
  ∃ xs : List R, xs.length≤s ∧ powerSum k xs=z ∧ ∃ u∈xs, IsUnit u

private theorem all_deep (I : Ideal R) (k : Nat)
    (hh : ∀ x : R, ¬IsUnit x → x^k∈I)
    (xs : List R) (h : ¬∃ u∈xs, IsUnit u) : powerSum k xs∈I := by
  induction xs with
  | nil => simpa [powerSum] using I.zero_mem
  | cons a l ih =>
    have ha : ¬IsUnit a := fun hu => h ⟨a,List.mem_cons_self,hu⟩
    have hl : ¬∃ u∈l, IsUnit u := fun ⟨u,hu,hy⟩ => h ⟨u,List.mem_cons_of_mem _ hu,hy⟩
    simpa [powerSum] using I.add_mem (hh _ ha) (ih hl)

private theorem adjust_word (I : Ideal R) (k : Nat)
    (hunit : ∀ x b : R, IsUnit x → b∈I → ∃ y, IsUnit y ∧ y^k=x^k+b)
    (xs : List R) (hu : ∃ u∈xs, IsUnit u) {b : R} (hb : b∈I) :
    ∃ ys : List R, ys.length=xs.length ∧ powerSum k ys=powerSum k xs+b ∧
      ∃ u∈ys, IsUnit u := by
  induction xs with
  | nil => simp at hu
  | cons x l ih =>
    by_cases hx : IsUnit x
    · obtain ⟨y,hy,he⟩ := hunit x b hx hb
      exact ⟨y::l,rfl,by simp [powerSum,he]; ring,⟨y,List.mem_cons_self,hy⟩⟩
    · obtain ⟨w,hw,hw'⟩ := hu
      have hl : w∈l := (List.mem_cons.mp hw).resolve_left (fun h => hx (h ▸ hw'))
      obtain ⟨ys,hn,he,hys⟩ := ih ⟨w,hl,hw'⟩
      obtain ⟨v,hv,hv'⟩ := hys
      refine ⟨x::ys,by simp [hn],?_,v,List.mem_cons_of_mem _ hv,hv'⟩
      change x^k+powerSum k ys=(x^k+powerSum k l)+b
      rw [he,add_assoc]

/-- Every ordinary width is already a primitive width. An eligible
test element t in I outside the deeper ideal D witnesses the zero
residue by a word containing a unit. -/
theorem widths_agree (I D : Ideal R) (k s : Nat) (hDI : D≤I)
    (hdeep : ∀ x : R, ¬IsUnit x → x^k∈D)
    (hunit : ∀ x b : R, IsUnit x → b∈I → ∃ y, IsUnit y ∧ y^k=x^k+b)
    (t : R) (ht : t∈Eligible k) (hti : t∈I) (htd : t∉D) :
    (∀ z : R, z∈Eligible k → Ordinary k s z) ↔ (∀ z : R, z∈Eligible k → Primitive k s z) := by
  constructor
  · intro h z hz
    obtain ⟨xs,hn,he⟩ := h z hz
    by_cases hx : ∃u∈xs,IsUnit u
    · exact ⟨xs,hn,he,hx⟩
    · have hzi : z∈I := hDI (he ▸ all_deep D k hdeep xs hx)
      obtain ⟨l,hl,hs⟩ := h t ht
      have htunit : ∃u∈l,IsUnit u := by
        by_contra hnon
        exact htd (hs ▸ all_deep D k hdeep l hnon)
      obtain ⟨y,hyn,hys,hyu⟩ := adjust_word I k hunit l htunit (I.sub_mem hzi hti)
      exact ⟨y,hyn.le.trans hl,by rw [hys,hs]; ring,hyu⟩
  · intro h z hz
    obtain ⟨xs,hn,he,_⟩ := h z hz
    exact ⟨xs,hn,he⟩

#print axioms widths_agree
end WaringLocal.FinitePrecision
