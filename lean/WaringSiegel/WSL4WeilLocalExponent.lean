import WaringSiegel.WSL4MajorRamanujamHenselTuple
import WaringSiegel.WSL2LocalPrimePowerQuotient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.CharP.Lemmas

noncomputable section
open IsLocalRing
open scoped NumberField
namespace WaringSiegel.WSL4Weil
set_option maxHeartbeats 1000000

/-- The tame/wild factorization uses the actual residue characteristic. -/
theorem local_nonunit_exponent_factorization
    {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [Finite (ResidueField R)]
    (m : ℕ) (hm : 0<m) (hmu : ¬IsUnit (m:R)) :
    ∃ p : ℕ,p.Prime ∧ CharP (ResidueField R) p ∧
      ∃r n : ℕ,1≤r ∧ 0<n ∧ m=n*p^r ∧ IsUnit (n:R) ∧ p^r≤m ∧ n≤m := by
  let p := ringChar (ResidueField R)
  have hp : p.Prime := CharP.prime_ringChar _
  letI : CharP (ResidueField R) p := inferInstance
  have hz : (m:ResidueField R)=0 := by
    have hh := (residue_ne_zero_iff_isUnit (m:R)).not.mpr hmu
    simpa only [map_natCast,not_not] using hh
  have hpm : p∣m := (CharP.cast_eq_zero_iff (ResidueField R) p m).mp hz
  let r := m.factorization p
  let n := ordCompl[p] m
  have hr : 1≤r := hp.factorization_pos_of_dvd hm.ne' hpm
  have hn : 0<n := Nat.ordCompl_pos p hm.ne'
  have heq : m=n*p^r := by
    simpa only [n,r,Nat.mul_comm] using (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hnu : IsUnit (n:R) := WSL4.nat_isUnit_of_residue_prime_not_dvd p n
    (Nat.not_dvd_ordCompl hp hm.ne')
  exact ⟨p,hp,inferInstance,r,n,hr,hn,heq,hnu,Nat.ordProj_le p hm.ne',Nat.ordCompl_le m p⟩

/-- Specialization at an actual finite place, directly from the original
hypothesis that the exponent belongs to the prime ideal. -/
theorem completion_exponent_factorization
    {K : Type*} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (m : ℕ) (hm : 0<m) (hvm : (m:𝓞 K)∈v.asIdeal) :
    ∃ p : ℕ,p.Prime ∧ CharP (ResidueField (v.adicCompletionIntegers K)) p ∧
      ∃r n : ℕ,1≤r ∧ 0<n ∧ m=n*p^r ∧
        IsUnit (n:v.adicCompletionIntegers K) ∧ p^r≤m ∧ n≤m := by
  letI := completionIntegers_isAdicComplete v
  letI := completionIntegers_residueFinite v
  apply local_nonunit_exponent_factorization m hm
  have hz : (m:ResidueField (v.adicCompletionIntegers K))=0 :=
    (completion_residue_natCast_eq_zero_iff v m).mpr hvm
  intro hu
  exact ((residue_ne_zero_iff_isUnit (m:v.adicCompletionIntegers K)).mpr hu)
    (by simpa only [map_natCast] using hz)

theorem composite_three_le_four_le (m : ℕ) (hm : 3≤m) (hprime : ¬m.Prime) : 4≤m := by
  by_contra h
  have he : m=3 := by omega
  subst m
  exact hprime Nat.prime_three
end WaringSiegel.WSL4Weil
#print axioms WaringSiegel.WSL4Weil.local_nonunit_exponent_factorization
#print axioms WaringSiegel.WSL4Weil.completion_exponent_factorization
#print axioms WaringSiegel.WSL4Weil.composite_three_le_four_le
