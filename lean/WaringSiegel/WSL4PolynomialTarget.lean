import WaringSiegel.WSL4PolynomialReduction
import WaringSiegel.WSL4RamanujamSmallResidue
import WaringSiegel.WSL4ArchRamanujamLargeResidue
import WaringSiegel.WSL4WeilLocalExponent

/-! # The unconditional polynomial Waring--Siegel bound

Both residue-degree ranges are proved for actual completed integer rings.
The residue characteristic and tame/wild factorization are extracted from
the original finite-place hypothesis. This discharges the remaining local
obligation and supplies a witness of the unchanged global target.
-/
noncomputable section
open IsLocalRing
open scoped NumberField Classical
namespace WaringSiegel.WSL4

theorem remainingLocalPowerClaim_verified : RemainingLocalPowerClaim := by
  intro K _ _ k hk hprime v hv a ha
  letI := completionIntegers_isAdicComplete v
  letI := completionIntegers_residueFinite v
  obtain ⟨p,hp,hchar,r,n,hr,hn,he,hnu,_,_⟩ :=
    WSL4Weil.completion_exponent_factorization v k (by omega) hv
  letI : Fact p.Prime := ⟨hp⟩
  letI : CharP (ResidueField (v.adicCompletionIntegers K)) p := hchar
  letI : Fintype (ResidueField (v.adicCompletionIntegers K)) := Fintype.ofFinite _
  letI : Algebra (ZMod p) (ResidueField (v.adicCompletionIntegers K)) := ZMod.algebra _ _
  let f := Module.finrank (ZMod p) (ResidueField (v.adicCompletionIntegers K))
  have hres : Nat.card (ResidueField (v.adicCompletionIntegers K))=p^f := by
    rw [Nat.card_eq_fintype_card,Module.card_eq_pow_finrank (K:=ZMod p),ZMod.card]
  have hk4 : 4≤n*p^r := by
    rw [←he]
    exact WSL4Weil.composite_three_le_four_le k hk hprime
  have ha' : a∈AddSubgroup.closure
      (Set.range (fun x : v.adicCompletionIntegers K => x^(n*p^r))) := by
    rw [←he]
    exact (WSL4Local.mem_powerGeneratedRing_iff k a).mp ha
  rw [he]
  rcases lt_or_ge f (n*p^r) with hf | hf
  · exact WSL4Local.small_residue_degree_power_list p n r f hn hnu hr hk4 hf hres a ha'
  · exact large_residue_degree_power_list p n r f hn hnu (by omega) hf hres a ha'

/-- The exact original polynomial target, with no additional premise. -/
theorem polynomialGlobalClaim_verified : PolynomialGlobalClaim :=
  polynomialGlobalClaim_of_remainingLocalPowerClaim remainingLocalPowerClaim_verified

/-- An explicit uniform form of the verified polynomial bound. -/
theorem uniform_polynomial_bound (k : ℕ) (hk : 2≤k) :
    UniformWaringSiegelBound k (8*k^5) := by
  intro K _ _
  exact polynomialGlobalClaim_verified K k hk

#print axioms remainingLocalPowerClaim_verified
#print axioms polynomialGlobalClaim_verified
#print axioms uniform_polynomial_bound
end WaringSiegel.WSL4
