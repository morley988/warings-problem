import Waring.LocalSolubilityCount

/-! # Concrete base congruences, with one variable fixed equal to one -/

noncomputable section
open scoped BigOperators
namespace Waring.LocalSolubility

theorem prime_base_with_one {k s p : ℕ} (hp : p.Prime) (hk : 0 < k) (hks : k ≤ s)
    (n : ℤ) : ∃ b : Fin s → ℤ,(p : ℤ) ∣ (1 : ℤ)^k+(∑ i,(b i)^k)-n := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := prime_sum_powers_length hp hk hks ((n : ZMod p)-1)
  refine ⟨fun i => (x i).val,?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  push_cast
  simp only [one_pow,ZMod.natCast_zmod_val,hx]
  ring

theorem ones_sum (k s m : ℕ) (hk : 0 < k) (hm : m ≤ s) :
    (∑ i : Fin s,(if i.val<m then (1 : ℤ) else 0)^k)=(m : ℤ) := by
  have hcard : ((Finset.univ : Finset (Fin s)).filter (fun i => i.val<m)).card=m := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_fin_lt_of_le hm
  have hpow (i : Fin s) : (if i.val<m then (1 : ℤ) else 0)^k=
      if i.val<m then (1 : ℤ) else 0 := by split_ifs <;> simp [hk.ne']
  simp_rw [hpow]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,hcard]

/-- B-1 further zero-or-one variables, with an initial one, represent every
residue modulo B. Larger variable sets are obtained by the same explicit
zero padding. -/
theorem base_with_one_of_modulus_le {k s B : ℕ} (hk : 0 < k) (hB : 0 < B)
    (hBs : B ≤ s+1) (n : ℤ) :
    ∃ b : Fin s → ℤ,(B : ℤ) ∣ (1 : ℤ)^k+(∑ i,(b i)^k)-n := by
  letI : NeZero B := ⟨hB.ne'⟩
  let m := ((n-1 : ℤ) : ZMod B).val
  have hm : m ≤ s := by have hh := ZMod.val_lt ((n-1 : ℤ) : ZMod B); omega
  refine ⟨fun i => if i.val<m then 1 else 0,?_⟩
  rw [one_pow,ones_sum k s m hk hm]
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ B).mp
  push_cast
  simp only [m,ZMod.natCast_zmod_val,Int.cast_sub,Int.cast_one]
  ring

#print axioms prime_base_with_one
#print axioms base_with_one_of_modulus_le
end Waring.LocalSolubility
