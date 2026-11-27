import WaringSiegel.WSL4LocalPowerRing
import WaringSiegel.WSL4ArchLocalFiniteAll
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Data.Fintype.Units

/-! # Cardinal constraints on proper finite-field subrings containing powers -/
noncomputable section
open scoped Classical
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1400000
variable {F : Type*} [Field F] [Finite F]

theorem finiteField_proper_subring_card_sq_le (S : Subring F) (hS : S≠⊤) :
    Nat.card S^2≤Nat.card F := by
  letI : Fintype S := Fintype.ofFinite S
  letI : Field S := Fintype.fieldOfDomain S
  obtain ⟨a,ha⟩ : ∃a : F,a∉S := by
    by_contra hh
    push_neg at hh
    exact hS (top_unique (fun x hx => hh x))
  let g : S × S → F := fun x => (x.1:F)+a*(x.2:F)
  have hinj : Function.Injective g := by
    intro x y h
    have h2 : (x.2:F)=(y.2:F) := by
      by_contra hne
      have hd : (x.2:F)-(y.2:F)≠0 := sub_ne_zero.mpr hne
      have he : (((y.1-x.1)/(x.2-y.2):S):F)=a := by
        change S.subtype ((y.1-x.1)/(x.2-y.2))=a
        rw [map_div₀,map_sub,map_sub]
        apply (div_eq_iff hd).mpr
        change (y.1:F)-(x.1:F)=a*((x.2:F)-(y.2:F))
        change (x.1:F)+a*(x.2:F)=(y.1:F)+a*(y.2:F) at h
        linear_combination -h
      exact ha (he ▸ ((y.1-x.1)/(x.2-y.2):S).property)
    apply Prod.ext
    · apply Subtype.ext
      change (x.1:F)+a*(x.2:F)=(y.1:F)+a*(y.2:F) at h
      rw [h2] at h
      exact add_right_cancel h
    · exact Subtype.ext h2
  simpa only [Nat.card_prod,pow_two] using Nat.card_le_card_of_injective g hinj

theorem finiteField_card_le_power_subring_card (n : ℕ) (hn : 0<n)
    (S : Subring F) (hpow : ∀x : F,x^n∈S) :
    Nat.card F-1≤n*(Nat.card S-1) := by
  letI : Fintype S := Fintype.ofFinite S
  letI : Field S := Fintype.fieldOfDomain S
  let H : Subgroup Fˣ := (powMonoidHom n : Fˣ →* Fˣ).range
  have hmem (u : H) : ((u:Fˣ):F)∈S := by
    obtain ⟨v,hv⟩ := u.property
    have he : (v:F)^n=((u:Fˣ):F) := by
      simpa only [powMonoidHom_apply,Units.val_pow_eq_pow_val] using
        congrArg (fun x : Fˣ => (x:F)) hv
    exact he ▸ hpow (v:F)
  let uS (u : H) : S := ⟨((u:Fˣ):F),hmem u⟩
  have hne (u : H) : uS u≠0 := by
    intro h
    have hh := congrArg S.subtype h
    exact (u:Fˣ).ne_zero hh
  let g : H → Sˣ := fun u => Units.mk0 (uS u) (hne u)
  have hinj : Function.Injective g := by
    intro u v h
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun w : Sˣ => ((w:S):F)) h
  have hcard : Nat.card H≤Nat.card S-1 := by
    simpa only [Nat.card_units] using Nat.card_le_card_of_injective g hinj
  have hindex : H.index≤n := by
    rw [show H.index=(Nat.card Fˣ).gcd n from IsCyclic.index_powMonoidHom_range Fˣ n]
    exact Nat.le_of_dvd hn (Nat.gcd_dvd_right _ _)
  calc
    Nat.card F-1=Nat.card Fˣ := (Nat.card_units F).symm
    _=Nat.card H*H.index := H.card_mul_index.symm
    _≤(Nat.card S-1)*n := Nat.mul_le_mul hcard hindex
    _=n*(Nat.card S-1) := Nat.mul_comm _ _

#print axioms finiteField_proper_subring_card_sq_le
#print axioms finiteField_card_le_power_subring_card
end WaringSiegel.WSL4
