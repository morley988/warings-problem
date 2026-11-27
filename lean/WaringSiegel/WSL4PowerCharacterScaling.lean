import WaringSiegel.WSL3LocalConductorShell
import WaringSiegel.WSL2LocalScaling

/-! # Uniformizer scaling of primitive quotient characters -/
noncomputable section
open IsLocalRing
open scoped BigOperators Classical
namespace WaringSiegel.WSL4Local

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

def uniformizerPowMulQuotient {π : R} (hπ : Irreducible π) (k n : ℕ) :
    (R⧸maximalIdeal R^n) →+ (R⧸maximalIdeal R^(n+k)) where
  toFun := Quotient.map' (fun x => π^k*x) (by
    intro x y h
    rw [Submodule.quotientRel_def] at h ⊢
    rw [← mul_sub]
    exact (uniformizer_power_cancel_mem hπ k n).mpr h)
  map_zero' := by change Ideal.Quotient.mk _ (π^k*0)=0; simp
  map_add' x y := by
    obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk _ (π^k*(u+v))=
      Ideal.Quotient.mk _ (π^k*u)+Ideal.Quotient.mk _ (π^k*v)
    rw [mul_add,map_add]

@[simp] theorem uniformizerPowMulQuotient_mk {π : R} (hπ : Irreducible π)
    (k n : ℕ) (x : R) :
    uniformizerPowMulQuotient hπ k n (Ideal.Quotient.mk _ x)=
      Ideal.Quotient.mk _ (π^k*x) := rfl

theorem uniformizerPowMulQuotient_injective {π : R} (hπ : Irreducible π) (k n : ℕ) :
    Function.Injective (uniformizerPowMulQuotient hπ k n) := by
  intro x y h
  obtain ⟨u,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  have hd := Ideal.Quotient.eq.mp h
  rw [← mul_sub] at hd
  exact (uniformizer_power_cancel_mem hπ k n).mp hd

def scaledQuotientCharacter {π : R} (hπ : Irreducible π) (k n : ℕ)
    (ψ : AddChar (R⧸maximalIdeal R^(n+k)) ℂ) : AddChar (R⧸maximalIdeal R^n) ℂ :=
  ψ.compAddMonoidHom (uniformizerPowMulQuotient hπ k n)

@[simp] theorem scaledQuotientCharacter_mk {π : R} (hπ : Irreducible π)
    (k n : ℕ) (ψ : AddChar (R⧸maximalIdeal R^(n+k)) ℂ) (x : R) :
    scaledQuotientCharacter hπ k n ψ (Ideal.Quotient.mk _ x)=
      ψ (Ideal.Quotient.mk _ (π^k*x)) := rfl

theorem scaledQuotientCharacter_conductor {π : R} (hπ : Irreducible π)
    (k n : ℕ) (ψ : AddChar (R⧸maximalIdeal R^(n+k)) ℂ)
    (hψ : quotientCharacterConductor (maximalIdeal R^(n+k)) ψ=maximalIdeal R^(n+k)) :
    quotientCharacterConductor (maximalIdeal R^n) (scaledQuotientCharacter hπ k n ψ)=
      maximalIdeal R^n := by
  ext a
  have he : a∈quotientCharacterConductor (maximalIdeal R^n) (scaledQuotientCharacter hπ k n ψ) ↔
      π^k*a∈quotientCharacterConductor (maximalIdeal R^(n+k)) ψ := by
    change (∀ x:R,ψ (Ideal.Quotient.mk _ (π^k*(a*x)))=1) ↔
      (∀ x:R,ψ (Ideal.Quotient.mk _ ((π^k*a)*x))=1)
    simp only [mul_assoc]
  rw [he,hψ]
  exact uniformizer_power_cancel_mem hπ k n

#print axioms uniformizerPowMulQuotient_injective
#print axioms scaledQuotientCharacter_conductor
end WaringSiegel.WSL4Local
