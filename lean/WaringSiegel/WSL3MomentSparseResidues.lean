import WaringSiegel.WSL3MomentSparsePolynomial

/-!
# A finite p-adic annulus partition for every integer source

The exceptional class consists of labels divisible by p^H.  Every other
class has fixed valuation e<H and fixed unit residue xi modulo p^c, and
its labels are exactly p^e(xi+p^c z).  There are at most 1+H p^c classes.
-/

noncomputable section
open Finset Polynomial GafniTao
open scoped BigOperators Classical

namespace WaringSiegel.WSL3

theorem integer_exists_valuation_unit_below (p H : ℕ) (hp : p.Prime)
    (n : ℤ) (hn : ¬ (p : ℤ)^H ∣ n) :
    ∃ e : Fin H, ∃ a : ℤ, Nat.Coprime p a.natAbs ∧ n=(p : ℤ)^e.val*a := by
  have hex : ∃ e : ℕ, ¬ (p : ℤ)^e ∣ n := ⟨H, hn⟩
  let m := Nat.find hex
  have hm : ¬ (p : ℤ)^m ∣ n := Nat.find_spec hex
  have hmH : m ≤ H := Nat.find_min' hex hn
  have hm0 : m ≠ 0 := by intro h; simp only [h, pow_zero, one_dvd, not_true_eq_false] at hm
  have hediv : (p : ℤ)^(m-1) ∣ n := by
    by_contra hh
    exact Nat.find_min hex (by dsimp [m]; omega) hh
  obtain ⟨a, ha⟩ := hediv
  refine ⟨⟨m-1, by omega⟩, a, ?_, ha⟩
  rw [hp.coprime_iff_not_dvd]
  intro hpa
  have hpaZ : (p : ℤ) ∣ a := by
    rw [← Int.dvd_natAbs]
    exact Int.natCast_dvd_natCast.mpr hpa
  obtain ⟨b, hb⟩ := hpaZ
  apply hm
  refine ⟨b, ?_⟩
  rw [ha, hb, ← mul_assoc, ← pow_succ]
  congr 2
  omega

theorem integer_unit_residue_decomposition (p c : ℕ) (hp : p.Prime) (hc : 1 ≤ c)
    (a : ℤ) (ha : Nat.Coprime p a.natAbs) :
    ∃ ξ : Fin (p^c), Nat.Coprime p ξ.val ∧ ∃ z : ℤ,
      a=(ξ.val : ℤ)+(p : ℤ)^c*z := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hpC : (0 : ℤ) < (p : ℤ)^c := by positivity
  let b := a % (p : ℤ)^c
  have hb0 : 0 ≤ b := Int.emod_nonneg _ (ne_of_gt hpC)
  have hbC : b < (p : ℤ)^c := Int.emod_lt_of_pos _ hpC
  let ξ : Fin (p^c) := ⟨b.toNat, by
    have hbcast : (b.toNat : ℤ) < ((p^c : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hb0]
      simpa only [Nat.cast_pow] using hbC
    exact_mod_cast hbcast⟩
  have hξb : (ξ.val : ℤ)=b := Int.toNat_of_nonneg hb0
  have hdecomp : a=(ξ.val : ℤ)+(p : ℤ)^c*(a/(p : ℤ)^c) := by
    rw [hξb]
    exact (Int.emod_add_ediv a ((p : ℤ)^c)).symm
  refine ⟨ξ, ?_, a/(p : ℤ)^c, hdecomp⟩
  rw [hp.coprime_iff_not_dvd] at ha ⊢
  intro hξ
  have hξZ : (p : ℤ) ∣ (ξ.val : ℤ) := Int.natCast_dvd_natCast.mpr hξ
  have hpc : (p : ℤ) ∣ (p : ℤ)^c := by
    simpa only [pow_one] using pow_dvd_pow (p : ℤ) hc
  have hpa : (p : ℤ) ∣ a := by
    rw [hdecomp]
    exact dvd_add hξZ (dvd_mul_of_dvd_left hpc _)
  exact ha (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hpa))

/-- A tag and exact affine coordinate, with a separately stated exceptional
class. No residue-value existence hypothesis is left to the consumer. -/
theorem integer_sparse_partition (p H c : ℕ) (hp : p.Prime) (hc : 1 ≤ c)
    {α : Type*} (labels : α → ℤ) :
    ∃ tag : α → Option (Fin H × Fin (p^c)), ∃ z : α → ℤ,
      (∀ x, tag x=none → (p : ℤ)^H ∣ labels x) ∧
      (∀ x e ξ, tag x=some (e,ξ) → Nat.Coprime p ξ.val ∧
        labels x=(p : ℤ)^e.val*((ξ.val : ℤ)+(p : ℤ)^c*z x)) := by
  have hex (x : α) : ∃ t : Option (Fin H × Fin (p^c)), ∃ z : ℤ,
      (t=none → (p : ℤ)^H ∣ labels x) ∧
      (∀ e ξ, t=some (e,ξ) → Nat.Coprime p ξ.val ∧
        labels x=(p : ℤ)^e.val*((ξ.val : ℤ)+(p : ℤ)^c*z)) := by
    by_cases hn : (p : ℤ)^H ∣ labels x
    · exact ⟨none, 0, fun _ => hn, by simp⟩
    · obtain ⟨e,a,ha,hxa⟩ := integer_exists_valuation_unit_below p H hp (labels x) hn
      obtain ⟨ξ,hξ,z,haz⟩ := integer_unit_residue_decomposition p c hp hc a ha
      refine ⟨some (e,ξ), z, by simp, ?_⟩
      intro e' ξ' hh
      have he : e=e' := congrArg Prod.fst (Option.some.inj hh)
      have hξ' : ξ=ξ' := congrArg Prod.snd (Option.some.inj hh)
      subst e'
      subst ξ'
      exact ⟨hξ, by rw [hxa,haz]⟩
  choose tag z h using hex
  exact ⟨tag,z,fun x hx => (h x).1 hx,fun x e ξ hx => (h x).2 e ξ hx⟩

theorem sparse_partition_zero_subsingleton (p H c : ℕ) {α : Type*}
    (labels : α → ℤ) (hinj : Function.Injective (fun x => (labels x : ZMod (p^H))))
    (tag : α → Option (Fin H × Fin (p^c)))
    (hz : ∀ x, tag x=none → (p : ℤ)^H ∣ labels x) :
    Subsingleton {x // tag x=none} := by
  refine ⟨?_⟩
  intro x y
  apply Subtype.ext
  apply hinj
  have hx : (labels x : ZMod (p^H))=0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
    exact hz x x.property
  have hy : (labels y : ZMod (p^H))=0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
    exact hz y y.property
  exact hx.trans hy.symm

theorem sparse_partition_coordinate_injective (p H c : ℕ) {α : Type*}
    (labels : α → ℤ) (hinj : Function.Injective (fun x => (labels x : ZMod (p^H))))
    (tag : α → Option (Fin H × Fin (p^c))) (z : α → ℤ)
    (hreg : ∀ x e ξ, tag x=some (e,ξ) →
      labels x=(p : ℤ)^e.val*((ξ.val : ℤ)+(p : ℤ)^c*z x))
    (e : Fin H) (ξ : Fin (p^c)) :
    Function.Injective (fun x : {x // tag x=some (e,ξ)} => (z x : ZMod (p^H))) := by
  intro x y hxy
  apply Subtype.ext
  apply hinj
  change (labels (x : α) : ZMod (p^H)) = (labels (y : α) : ZMod (p^H))
  rw [hreg x e ξ x.property, hreg y e ξ y.property]
  push_cast
  change (z (x : α) : ZMod (p^H)) = (z (y : α) : ZMod (p^H)) at hxy
  rw [hxy]

#print axioms integer_sparse_partition

end WaringSiegel.WSL3
