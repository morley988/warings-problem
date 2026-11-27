import Waring.EndgameCompletionPrimePowers
import Waring.PolicyCompletionUnityRoots

/-!
# Power fibers at prime-power moduli

The roots-of-unity theorem controls unit fibers, including primes dividing
the exponent.  Extracting the valuation of one root then controls every
nonunit fiber, with the gcd of the target retained explicitly.
-/

noncomputable section
open scoped BigOperators Classical

namespace Waring.EndgameCompletion

theorem unit_power_fiber_card_le {q d : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) :
    (Finset.univ.filter fun x : ZMod q => x^d=(u : ZMod q)^d).card ≤
      (PolicyCompletionUnityRoots.unityRoots d q).card := by
  apply Finset.card_le_card_of_injOn (fun x : ZMod q => (x*(u⁻¹ : (ZMod q)ˣ)).val)
  · intro x hx
    apply PolicyCompletionUnityRoots.mem_unityRoots.mpr
    refine ⟨ZMod.val_lt _, ?_⟩
    rw [ZMod.natCast_zmod_val, mul_pow, (Finset.mem_filter.mp hx).2,
      ← mul_pow, Units.mul_inv, one_pow]
  · intro x _ y _ hxy
    have h := ZMod.val_injective _ hxy
    have hh := congrArg (fun z : ZMod q => z*(u : ZMod q)) h
    simpa only [mul_assoc, Units.inv_mul, mul_one] using hh

theorem primepower_unit_power_fiber_card_le {p d : ℕ} (hp : p.Prime)
    (hd : 0 < d) (l : ℕ) [NeZero (p^l)] (u : (ZMod (p^l))ˣ) :
    (Finset.univ.filter fun x : ZMod (p^l) => x^d=(u : ZMod (p^l))^d).card ≤
      2*d :=
  (unit_power_fiber_card_le u).trans
    (PolicyCompletionUnityRoots.unityRoots_prime_power_card_le hd hp l)

/-- Cancelling an exact prime-power factor from a congruence. -/
theorem primepower_mul_congr_cancel {p l v x y : ℕ} (hp : 0 < p)
    (hvl : v ≤ l)
    (h : ((p^v*x : ℕ) : ZMod (p^l))=((p^v*y : ℕ) : ZMod (p^l))) :
    (x : ZMod (p^(l-v)))=(y : ZMod (p^(l-v))) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hpow : p^l=p^v*p^(l-v) := by rw [← pow_add, Nat.add_sub_of_le hvl]
  rw [hpow] at hm
  exact Nat.ModEq.mul_left_cancel' (pow_pos hp _).ne' hm

/-- A chosen root with valuation w controls the entire power fiber.  The
second coordinate below records the lifts lost on reducing the quotient. -/
theorem primepower_power_fiber_card_le_of_root {p d l w c : ℕ}
    (hp : p.Prime) (hd : 0 < d) (hpc : ¬ p ∣ c) (hwd : w*d < l)
    [NeZero (p^l)] :
    (Finset.univ.filter fun x : ZMod (p^l) =>
      x^d=((p^w*c : ℕ) : ZMod (p^l))^d).card ≤ 2*d*p^(w*d) := by
  letI : NeZero (p^(l-w*d)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let Q := p^(l-w*d)
  let A := Finset.univ.filter fun x : ZMod (p^l) =>
    x^d=((p^w*c : ℕ) : ZMod (p^l))^d
  have hcunit : IsUnit (c : ZMod Q) := by
    apply (ZMod.isUnit_iff_coprime _ _).mpr
    exact (hp.coprime_iff_not_dvd.mpr hpc).symm.pow_right _
  let u := hcunit.unit
  let B := Finset.univ.filter fun y : ZMod Q => y^d=(u : ZMod Q)^d
  have hxcong (x : ZMod (p^l)) (hx : x∈A) :
      x.val^d ≡ (p^w*c)^d [MOD p^l] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using (Finset.mem_filter.mp hx).2
  have hxdiv (x : ZMod (p^l)) (hx : x∈A) : p^w ∣ x.val := by
    apply (Nat.pow_dvd_pow_iff hd.ne').mp
    have ht : p^(w*d) ∣ x.val^d :=
      ((hxcong x hx).dvd_iff (pow_dvd_pow p hwd.le)).mpr (by
        rw [mul_pow,← pow_mul]
        exact dvd_mul_right _ _)
    simpa only [pow_mul] using ht
  have hxquot (x : ZMod (p^l)) (hx : x∈A) :
      ((x.val/p^w : ℕ) : ZMod Q)^d=(u : ZMod Q)^d := by
    have hm := hxcong x hx
    have hxrec : x.val=p^w*(x.val/p^w) := (Nat.mul_div_cancel' (hxdiv x hx)).symm
    rw [hxrec,mul_pow,mul_pow,← pow_mul] at hm
    have hz := primepower_mul_congr_cancel hp.pos hwd.le
      ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hm)
    simpa only [Nat.cast_pow,IsUnit.unit_spec] using hz
  have hinj : A.card ≤ (B ×ˢ Finset.range (p^(w*d))).card := by
    apply Finset.card_le_card_of_injOn (fun x : ZMod (p^l) =>
      (((x.val/p^w : ℕ) : ZMod Q),(x.val/p^w)/Q))
    · intro x hx
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxquot x hx⟩,?_⟩
      apply Finset.mem_range.mpr
      apply (Nat.div_lt_iff_lt_mul (pow_pos hp.pos _)).mpr
      have hlt : x.val/p^w < p^l := (Nat.div_le_self _ _).trans_lt x.val_lt
      convert hlt using 1
      dsimp [Q]
      rw [← pow_add,Nat.add_sub_of_le hwd.le]
    · intro x hx y hy hxy
      apply ZMod.val_injective
      have hm := congrArg Prod.fst hxy
      have hq := congrArg Prod.snd hxy
      change (x.val/p^w)/Q=(y.val/p^w)/Q at hq
      have hmod : (x.val/p^w)%Q=(y.val/p^w)%Q :=
        (ZMod.natCast_eq_natCast_iff' _ _ _).mp hm
      have hquot : x.val/p^w=y.val/p^w := by
        calc
          _ = (x.val/p^w)%Q+Q*((x.val/p^w)/Q) := (Nat.mod_add_div _ _).symm
          _ = (y.val/p^w)%Q+Q*((y.val/p^w)/Q) := by rw [hmod,hq]
          _ = _ := Nat.mod_add_div _ _
      calc
        x.val=p^w*(x.val/p^w) := (Nat.mul_div_cancel' (hxdiv x hx)).symm
        _ = p^w*(y.val/p^w) := by rw [hquot]
        _ = y.val := Nat.mul_div_cancel' (hxdiv y hy)
  calc
    _ = A.card := rfl
    _ ≤ B.card*p^(w*d) := by simpa only [Finset.card_product,Finset.card_range] using hinj
    _ ≤ 2*d*p^(w*d) := Nat.mul_le_mul_right _ (primepower_unit_power_fiber_card_le hp hd _ u)

/-- All power fibers, including nonunits and the zero target. -/
theorem primepower_power_fiber_card_le {p d : ℕ} (hp : p.Prime)
    (hd : 0 < d) (l : ℕ) [NeZero (p^l)] (b : ZMod (p^l)) :
    (Finset.univ.filter fun x : ZMod (p^l) => x^d=b).card ≤
      2*d*Nat.gcd b.val (p^l) := by
  classical
  let A := Finset.univ.filter fun x : ZMod (p^l) => x^d=b
  by_cases hb : b=0
  · subst b
    simp only [ZMod.val_zero,Nat.gcd_zero_left]
    calc
      _ ≤ Fintype.card (ZMod (p^l)) := (Finset.card_filter_le _ _).trans_eq Finset.card_univ
      _ = p^l := ZMod.card _
      _ ≤ 2*d*p^l := by nlinarith [pow_pos hp.pos l]
  by_cases hA : A.Nonempty
  · obtain ⟨x₀,hx₀⟩ := hA
    have hx₀pow : x₀^d=b := (Finset.mem_filter.mp hx₀).2
    have hx₀val : x₀.val≠0 := by
      intro hzero
      have hxzero : x₀=0 := ZMod.val_injective _ (by simpa only [ZMod.val_zero] using hzero)
      apply hb
      rw [← hx₀pow,hxzero,zero_pow hd.ne']
    obtain ⟨w,c,hpc,hfactor⟩ := Nat.exists_eq_pow_mul_and_not_dvd hx₀val p hp.ne_one
    have hwd : w*d<l := by
      by_contra h
      have hdiv : p^l ∣ x₀.val^d := by
        rw [hfactor,mul_pow,← pow_mul]
        exact (pow_dvd_pow p (by omega : l≤w*d)).trans (dvd_mul_right _ _)
      have hz := (ZMod.natCast_eq_zero_iff (x₀.val^d) (p^l)).mpr hdiv
      apply hb
      simpa only [Nat.cast_pow,ZMod.natCast_zmod_val,hx₀pow] using hz
    have hgcd : Nat.gcd b.val (p^l)=p^(w*d) := by
      have hm : x₀.val^d ≡ b.val [MOD p^l] := by
        apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
        simpa only [Nat.cast_pow,ZMod.natCast_zmod_val] using hx₀pow
      rw [← hm.gcd_eq,hfactor,mul_pow,← pow_mul]
      have hpows : p^l=p^(w*d)*p^(l-w*d) := by rw [← pow_add,Nat.add_sub_of_le hwd.le]
      rw [hpows,Nat.gcd_mul_left]
      have hcop : Nat.Coprime (c^d) (p^(l-w*d)) :=
        ((hp.coprime_iff_not_dvd.mpr hpc).symm.pow_left _).pow_right _
      rw [hcop.gcd_eq_one,Nat.mul_one]
    have heq : b=((p^w*c : ℕ) : ZMod (p^l))^d := by
      rw [← hfactor,ZMod.natCast_zmod_val,hx₀pow]
    rw [hgcd,heq]
    exact primepower_power_fiber_card_le_of_root hp hd hpc hwd
  · have hz : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    change A.card≤_
    rw [hz,Finset.card_empty]
    exact Nat.zero_le _

#print axioms primepower_power_fiber_card_le

end Waring.EndgameCompletion
