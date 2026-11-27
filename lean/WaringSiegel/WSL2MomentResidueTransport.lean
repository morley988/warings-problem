import WaringSiegel.WSL2MomentVinogradov
import WaringSiegel.WSL2MomentProgressions
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finsupp.Indicator

/-!
# Exact arithmetic transport toward the native integer p-adic VMVT source

These are closed algebraic and counting lemmas, not a number-field VMVT
estimate.  An actual quotient equivalence with `ZMod q` is an explicit input;
existence of a suitable unramified residue-degree-one prime is not asserted.
The integer representatives preserve all power-sum congruences, lower-modulus
residues are compatible for nested ideals, and sufficiently deep residue maps
are injective on the actual archimedean box by the proved norm separation.
-/

noncomputable section
open scoped BigOperators NumberField nonZeroDivisors Classical

namespace WaringSiegel.WSL2

section Rings
variable {R S α : Type*} [CommRing R] [CommRing S] [Fintype α]

theorem VinogradovEquations.map (f : R→+*S) (k s : ℕ) (nodes : α→R)
    (x y : Fin s→α) (h : VinogradovEquations k s nodes x y) :
    VinogradovEquations k s (fun a=>f (nodes a)) x y := by
  intro j
  simpa only [map_sum,map_pow] using congrArg f (h j)

theorem vinogradovCount_le_map (f : R→+*S) (k s : ℕ) (nodes : α→R) :
    vinogradovCount k s nodes ≤ vinogradovCount k s (fun a=>f (nodes a)) := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hmem,heq⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hmem, heq.map f k s nodes p.1 p.2⟩

def quotientIntegerRepresentative (I : Ideal R) {q : ℕ} [NeZero q]
    (e : (R⧸I)≃+*ZMod q) (x : R) : ℤ := (e (Ideal.Quotient.mk I x)).val

theorem quotientIntegerRepresentative_cast (I : Ideal R) {q : ℕ} [NeZero q]
    (e : (R⧸I)≃+*ZMod q) (x : R) :
    (quotientIntegerRepresentative I e x : ZMod q)=e (Ideal.Quotient.mk I x) := by
  simp only [quotientIntegerRepresentative,Int.cast_natCast,ZMod.natCast_zmod_val]

theorem quotientIntegerRepresentative_sub_mem (I : Ideal R) {q : ℕ} [NeZero q]
    (e : (R⧸I)≃+*ZMod q) (x : R) :
    x-(quotientIntegerRepresentative I e x : R)∈I := by
  apply Ideal.Quotient.eq.mp
  apply e.injective
  rw [map_intCast,map_intCast,quotientIntegerRepresentative_cast]

/-- The same integer representative has the correct residue in every nested
quotient.  Compatibility is proved from ideal inclusion and unital ring maps. -/
theorem quotientIntegerRepresentative_lower_cast (I J : Ideal R) (hIJ : I≤J)
    {q r : ℕ} [NeZero q] [NeZero r]
    (e : (R⧸I)≃+*ZMod q) (f : (R⧸J)≃+*ZMod r) (x : R) :
    (quotientIntegerRepresentative I e x : ZMod r)=f (Ideal.Quotient.mk J x) := by
  have heq : Ideal.Quotient.mk J x=Ideal.Quotient.mk J (quotientIntegerRepresentative I e x : R) :=
    Ideal.Quotient.eq.mpr (hIJ (quotientIntegerRepresentative_sub_mem I e x))
  have hf := congrArg f heq
  simpa only [map_intCast] using hf.symm

theorem quotientIntegerRepresentative_power_congruences (I : Ideal R) {q : ℕ} [NeZero q]
    (e : (R⧸I)≃+*ZMod q) (k s : ℕ) (nodes : α→R)
    (x y : Fin s→α) (h : VinogradovEquations k s nodes x y) :
    ∀j : Fin k,
      ((∑i, (quotientIntegerRepresentative I e (nodes (x i)))^(j.val+1) : ℤ) : ZMod q) =
        ((∑i, (quotientIntegerRepresentative I e (nodes (y i)))^(j.val+1) : ℤ) : ZMod q) := by
  have hm := h.map (e.toRingHom.comp (Ideal.Quotient.mk I)) k s nodes x y
  intro j
  simpa only [Int.cast_sum,Int.cast_pow,quotientIntegerRepresentative_cast,RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe] using hm j

theorem vinogradovCount_le_integer_modular_count (I : Ideal R) {q : ℕ} [NeZero q]
    (e : (R⧸I)≃+*ZMod q) (k s : ℕ) (nodes : α→R) :
    vinogradovCount k s nodes ≤
      vinogradovCount k s (fun a=>(quotientIntegerRepresentative I e (nodes a) : ZMod q)) := by
  simpa only [quotientIntegerRepresentative_cast,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe]
    using vinogradovCount_le_map (e.toRingHom.comp (Ideal.Quotient.mk I)) k s nodes

end Rings

section NumberField
variable {K : Type*} [Field K] [NumberField K]

/-- Ideal reduction is literally injective on a box once the ideal norm
exceeds the maximum possible norm of a nonzero difference. -/
theorem ideal_quotient_injective_on_box (I : Ideal (𝓞 K)) (P : ℝ) (hP : 0≤P)
    (hdeep : (2*P)^(Module.finrank ℚ K)<(Ideal.absNorm I:ℝ)) :
    Set.InjOn (Ideal.Quotient.mk I)
      {x : 𝓞 K | ∀v : NumberField.InfinitePlace K, v (x:K)≤P} := by
  intro x hx y hy heq
  by_contra hxy
  have hdiff : x-y∈I := Ideal.Quotient.eq.mp heq
  have hlo := ideal_absNorm_le_element_norm I hdiff (sub_ne_zero.mpr hxy)
  have hup := absNorm_le_box (show 0≤2*P by positivity) (fun v=>place_sub_le_twice hx hy v)
  exact (not_le_of_gt hdeep) (hlo.trans hup)

/-- The actual lower-residue map of the chosen integer labels is injective.
This is the singleton conditioning input for native Corollary 3.2. -/
theorem integer_representatives_lower_residue_injective
    {α : Type*} (I J : Ideal (𝓞 K)) (hIJ : I≤J)
    {q r : ℕ} [NeZero q] [NeZero r]
    (e : ((𝓞 K)⧸I)≃+*ZMod q) (f : ((𝓞 K)⧸J)≃+*ZMod r)
    (P : ℝ) (hP : 0≤P) (hdeep : (2*P)^(Module.finrank ℚ K)<(Ideal.absNorm J:ℝ))
    (nodes : α→𝓞 K) (hnodes : Function.Injective nodes)
    (hbox : ∀x, ∀v : NumberField.InfinitePlace K, v (nodes x:K)≤P) :
    Function.Injective (fun x=>(quotientIntegerRepresentative I e (nodes x) : ZMod r)) := by
  intro x y heq
  apply hnodes
  apply ideal_quotient_injective_on_box J P hP hdeep (hbox x) (hbox y)
  apply f.injective
  simpa only [quotientIntegerRepresentative_lower_cast I J hIJ e f] using heq

theorem integer_representatives_injective
    {α : Type*} (I J : Ideal (𝓞 K)) (hIJ : I≤J)
    {q r : ℕ} [NeZero q] [NeZero r]
    (e : ((𝓞 K)⧸I)≃+*ZMod q) (f : ((𝓞 K)⧸J)≃+*ZMod r)
    (P : ℝ) (hP : 0≤P) (hdeep : (2*P)^(Module.finrank ℚ K)<(Ideal.absNorm J:ℝ))
    (nodes : α→𝓞 K) (hnodes : Function.Injective nodes)
    (hbox : ∀x, ∀v : NumberField.InfinitePlace K, v (nodes x:K)≤P) :
    Function.Injective (fun x=>quotientIntegerRepresentative I e (nodes x)) := by
  intro x y heq
  apply integer_representatives_lower_residue_injective I J hIJ e f P hP hdeep nodes hnodes hbox
  exact congrArg (fun z : ℤ=>(z:ZMod r)) heq

end NumberField
end WaringSiegel.WSL2
