import WaringLinear.EvenStationaryBranch
import WaringLinear.OddStationaryBranch
import WaringLinear.MiddleConductor
import WaringLinear.ProductConductor

/-! # Complete polynomial sums on principal finite-conductor branches -/
noncomputable section
namespace WaringLinear
open Polynomial IsLocalRing
open scoped Classical BigOperators
variable {R : Type*} [CommRing R] [IsDomain R]

theorem even_principal_stationary (d : R) (hd : d≠0)
    [IsLocalRing (R ⧸ Ideal.span {d^2})] [Fintype (R ⧸ Ideal.span {d^2})]
    (ψ : AddChar (R ⧸ Ideal.span {d^2}) ℂ) (hψ : ψ.IsPrimitive)
    (f : (R ⧸ Ideal.span {d^2})[X]) (y : R ⧸ Ideal.span {d^2})
    (hy : residue _ (f.derivative.eval y)=0) (hder : IsUnit (f.derivative.derivative.eval y)) :
    ∃ a, residue _ a=residue _ y ∧ f.derivative.eval a=0 ∧
      (∑ x ∈ Finset.univ.filter (fun x => residue _ x=residue _ y), ψ (f.eval x)) =
        (Real.sqrt (Fintype.card (R ⧸ Ideal.span {d^2})):ℂ)*ψ (f.eval a) :=
  even_stationary_branch ψ hψ f (Ideal.Quotient.mk (Ideal.span {d^2}) d) y
    (middle_conductor_annihilator d hd) hy hder

/-- In particular choose c=π^(r+1), d=π^r at odd conductor 2r+1, r≥1. -/
theorem odd_principal_stationary (c d : R) (hc : c≠0) (hd : d≠0) (hdc : d∣c) (hcd : c∣d^2)
    [IsLocalRing (R ⧸ Ideal.span {c*d})] [Fintype (R ⧸ Ideal.span {c*d})]
    (ψ : AddChar (R ⧸ Ideal.span {c*d}) ℂ) (hψ : ψ.IsPrimitive)
    (f : (R ⧸ Ideal.span {c*d})[X]) (y : R ⧸ Ideal.span {c*d})
    (hy : residue _ (f.derivative.eval y)=0) (hder : IsUnit (f.derivative.derivative.eval y)) :
    ∃ a, residue _ a=residue _ y ∧ f.derivative.eval a=0 ∧
      let phase := oddGaussPhase ψ ((hasseDeriv 2 f).eval a) (Ideal.Quotient.mk _ d)
      ‖phase‖=1 ∧
      (∑ x ∈ Finset.univ.filter (fun x => residue _ x=residue _ y), ψ (f.eval x)) =
        (Real.sqrt (Fintype.card (R ⧸ Ideal.span {c*d})):ℂ)*ψ (f.eval a)*phase := by
  obtain ⟨hn,hm,ha,hb⟩ := odd_conductor_conditions c d hc hd hdc hcd
  exact odd_stationary_branch ψ hψ f (Ideal.Quotient.mk _ c) (Ideal.Quotient.mk _ d) y hn hm ha hb hy hder

#print axioms even_principal_stationary
#print axioms odd_principal_stationary
end WaringLinear
