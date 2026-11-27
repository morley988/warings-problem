import Waring.External.GafniTao.WooleySection7Arithmetic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The exact p-adic separation used in Wooley Section 7

For a separated pair of least nonnegative residue representatives, this
file extracts the literal factorization `xi - eta = omega * p^gamma`, with
`gamma < nu` and `omega` prime to `p`.  This is the arithmetic assertion
immediately preceding equation (7.3).
-/

namespace GafniTao

noncomputable section

/-- Lean4.24 compatibility: the natural number with its maximal p-power
factor removed, expressed by the literal valuation quotient. -/
def wooleyPadicUnitQuotient (n p : ℕ) : ℕ := n / p ^ padicValNat p n

private theorem wooleyPadicUnitQuotient_factorization (n p : ℕ) :
    p ^ padicValNat p n * wooleyPadicUnitQuotient n p = n :=
  Nat.mul_div_cancel' pow_padicValNat_dvd

def wooleyResidueDifference {p a b : ℕ}
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) : ℤ :=
  (xi.val : ℤ) - (eta.val : ℤ)

def wooleyResidueValuation {p a b : ℕ}
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) : ℕ :=
  padicValNat p (wooleyResidueDifference xi eta).natAbs

def wooleyResidueUnitNat {p a b : ℕ}
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) : ℕ :=
  wooleyPadicUnitQuotient (wooleyResidueDifference xi eta).natAbs p

def wooleyResidueUnit {p a b : ℕ}
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) : ℤ :=
  Int.sign (wooleyResidueDifference xi eta) *
    (wooleyResidueUnitNat xi eta : ℤ)

theorem wooleyResidueDifference_ne_zero_of_separated
    {p a b nu : ℕ} {xi : ZMod (p ^ a)} {eta : ZMod (p ^ b)}
    (hsep : wooleyResiduesSeparated nu xi eta) :
    wooleyResidueDifference xi eta ≠ 0 := by
  intro hzero
  have hval : xi.val = eta.val := by
    exact_mod_cast (sub_eq_zero.mp hzero)
  exact hsep (by simp [hval])

theorem wooleyResidueDifference_factorization
    {p a b : ℕ} (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) :
    wooleyResidueDifference xi eta =
      wooleyResidueUnit xi eta *
        (p : ℤ) ^ wooleyResidueValuation xi eta := by
  let d := wooleyResidueDifference xi eta
  have hnat :
      p ^ padicValNat p d.natAbs * wooleyPadicUnitQuotient d.natAbs p = d.natAbs :=
    wooleyPadicUnitQuotient_factorization d.natAbs p
  have hsign : (Int.sign d) * (d.natAbs : ℤ) = d :=
    Int.sign_mul_natAbs d
  change d =
    (Int.sign d * (wooleyPadicUnitQuotient d.natAbs p : ℤ)) *
      (p : ℤ) ^ padicValNat p d.natAbs
  calc
    d = Int.sign d * (d.natAbs : ℤ) := hsign.symm
    _ = Int.sign d *
        ((wooleyPadicUnitQuotient d.natAbs p : ℤ) *
          (p : ℤ) ^ padicValNat p d.natAbs) := by
      congr 1
      exact_mod_cast (by simpa only [Nat.mul_comm] using hnat.symm)
    _ = _ := by ring

theorem wooleyResidueUnitNat_coprime
    {p a b nu : ℕ} (hp : p.Prime)
    {xi : ZMod (p ^ a)} {eta : ZMod (p ^ b)}
    (hsep : wooleyResiduesSeparated nu xi eta) :
    Nat.Coprime p (wooleyResidueUnitNat xi eta) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [hp.coprime_iff_not_dvd]
  let n := (wooleyResidueDifference xi eta).natAbs
  have hn : n ≠ 0 := Int.natAbs_ne_zero.mpr
    (wooleyResidueDifference_ne_zero_of_separated hsep)
  change ¬p ∣ wooleyPadicUnitQuotient n p
  intro hdiv
  apply pow_succ_padicValNat_not_dvd (p := p) hn
  have hmul := Nat.mul_dvd_mul_left (p ^ padicValNat p n) hdiv
  simpa only [← pow_succ,wooleyPadicUnitQuotient_factorization] using hmul

theorem wooleyResidueValuation_lt
    {p a b nu : ℕ} (hp : p.Prime)
    {xi : ZMod (p ^ a)} {eta : ZMod (p ^ b)}
    (hsep : wooleyResiduesSeparated nu xi eta) :
    wooleyResidueValuation xi eta < nu := by
  letI : Fact p.Prime := ⟨hp⟩
  let d := wooleyResidueDifference xi eta
  have hd : d ≠ 0 := wooleyResidueDifference_ne_zero_of_separated hsep
  have hn : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd
  have hnotdvd : ¬ p ^ nu ∣ d.natAbs := by
    intro hdvd
    have hdvdInt : ((p ^ nu : ℕ) : ℤ) ∣ d := by
      rw [← Int.dvd_natAbs]
      exact Int.natCast_dvd_natCast.mpr hdvd
    have hmodeq : xi.val ≡ eta.val [MOD p ^ nu] := by
      rw [Nat.modEq_iff_dvd]
      simpa [d, wooleyResidueDifference, sub_eq_add_neg,
        add_comm] using (Int.dvd_neg.mpr hdvdInt)
    exact hsep hmodeq
  have hnotle : ¬ nu ≤ padicValNat p d.natAbs := by
    intro hle
    exact hnotdvd ((padicValNat_dvd_iff_le hn).2 hle)
  exact Nat.lt_of_not_ge hnotle

theorem wooley_padic_separation
    {p a b nu : ℕ} (hp : p.Prime)
    {xi : ZMod (p ^ a)} {eta : ZMod (p ^ b)}
    (hsep : wooleyResiduesSeparated nu xi eta) :
    ∃ gamma : ℕ, ∃ omega : ℤ,
      gamma < nu ∧ Nat.Coprime p omega.natAbs ∧
        wooleyResidueDifference xi eta = omega * (p : ℤ) ^ gamma := by
  refine ⟨wooleyResidueValuation xi eta,
    wooleyResidueUnit xi eta, wooleyResidueValuation_lt hp hsep, ?_,
    wooleyResidueDifference_factorization xi eta⟩
  have hcop := wooleyResidueUnitNat_coprime hp hsep
  have hd : wooleyResidueDifference xi eta ≠ 0 :=
    wooleyResidueDifference_ne_zero_of_separated hsep
  simpa [wooleyResidueUnit, wooleyResidueUnitNat,
    Int.natAbs_mul, Int.natAbs_sign, hd] using hcop


end

end GafniTao
