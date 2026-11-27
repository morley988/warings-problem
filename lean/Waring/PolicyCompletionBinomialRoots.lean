import Waring.PolicyCompletionUnityRoots

/-!
# The coprime binomial quotient in the basic coefficient estimate

Vaughan--Wooley (1995), (4.8)--(4.9), requires the number of classes n
modulo q for which q divides ((n+l)^d-n^d)/l, with the coprimality conditions
inherited from extracting gcd(m1,m2).  Sending n to (n+l)/n modulo l*q
injects these classes into the d-th roots of unity.  This proof retains
the coprimality (n,l)=1 from the original change of variables; it does not
assume that the polynomial is nonsingular at primes dividing d or l.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBinomialRoots
open PolicyCompletionUnityRoots

def differenceQuotient (d : ℕ) (n l : ℤ) : ℤ := ((n+l)^d-n^d)/l

theorem shift_dvd_difference (d : ℕ) (n l : ℤ) : l∣(n+l)^d-n^d := by
  simpa only [add_sub_cancel_left] using sub_dvd_pow_sub_pow (n+l) n d

theorem quotient_divisibility_iff (d : ℕ) (n l q : ℤ) :
    q∣differenceQuotient d n l ↔ l*q∣(n+l)^d-n^d := by
  exact Int.dvd_div_iff_mul_dvd (shift_dvd_difference d n l)

def ratio (q l n : ℕ) : ZMod (l*q) := ((n+l : ℕ) : ZMod (l*q))*(n : ZMod (l*q))⁻¹

theorem ratio_pow_eq_one {d q l n : ℕ} (hcop : Nat.Coprime n (l*q))
    (hdiv : (q : ℤ)∣differenceQuotient d n l) : (ratio q l n)^d=1 := by
  have hdiv' := (quotient_divisibility_iff d n l q).mp hdiv
  have heq : ((n+l : ℕ) : ZMod (l*q))^d=(n : ZMod (l*q))^d := by
    apply sub_eq_zero.mp
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (((n : ℤ)+(l : ℤ))^d-(n : ℤ)^d) (l*q)).mpr (by
        simpa only [Nat.cast_mul] using hdiv')
    simpa only [Int.cast_sub,Int.cast_pow,Int.cast_add,Int.cast_natCast,Nat.cast_add] using hh
  unfold ratio
  rw [mul_pow,heq,← mul_pow,ZMod.mul_inv_of_unit _
    ((ZMod.isUnit_iff_coprime n (l*q)).mpr hcop),one_pow]

/-- The ratio remembers n modulo q, even when l and q have common factors. -/
theorem ratio_eq_implies_mod_eq {q l n m : ℕ} (hl : 0<l)
    (hn : Nat.Coprime n (l*q)) (hm : Nat.Coprime m (l*q))
    (h : ratio q l n=ratio q l m) : n%q=m%q := by
  have hninv := ZMod.inv_mul_of_unit (n : ZMod (l*q)) ((ZMod.isUnit_iff_coprime n (l*q)).mpr hn)
  have hminv := ZMod.inv_mul_of_unit (m : ZMod (l*q)) ((ZMod.isUnit_iff_coprime m (l*q)).mpr hm)
  have hcross : ((n : ZMod (l*q))+l)*m=((m : ZMod (l*q))+l)*n := by
    have hh := congrArg (fun x : ZMod (l*q) => x*((n : ZMod (l*q))*m)) h
    change (((n+l : ℕ) : ZMod (l*q))*(n : ZMod (l*q))⁻¹)*
      ((n : ZMod (l*q))*m)=
      (((m+l : ℕ) : ZMod (l*q))*(m : ZMod (l*q))⁻¹)*
      ((n : ZMod (l*q))*m) at hh
    push_cast at hh
    calc
      ((n : ZMod (l*q))+l)*m =
          (((n : ZMod (l*q))+l)*(n : ZMod (l*q))⁻¹)*(n*m) := by
        calc
          _ = ((n+l)*((n : ZMod (l*q))⁻¹*n))*m := by rw [hninv]; ring
          _ = _ := by ring
      _ = (((m : ZMod (l*q))+l)*(m : ZMod (l*q))⁻¹)*(n*m) := hh
      _ = ((m : ZMod (l*q))+l)*n := by
        calc
          _ = ((m+l)*((m : ZMod (l*q))⁻¹*m))*n := by ring
          _ = _ := by rw [hminv]; ring
  have hz : (((l : ℤ)*((m : ℤ)-n) : ℤ) : ZMod (l*q))=0 := by
    push_cast
    linear_combination hcross
  have hdiv : (l : ℤ)*(q : ℤ)∣(l : ℤ)*((m : ℤ)-n) := by
    simpa only [Nat.cast_mul] using
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((l : ℤ)*((m : ℤ)-n)) (l*q)).mp hz
  have hqdiv : (q : ℤ)∣(m : ℤ)-n :=
    (Int.mul_dvd_mul_iff_left (by exact_mod_cast hl.ne')).mp hdiv
  have heq : (n : ZMod q)=(m : ZMod q) := by
    simpa only [Int.cast_natCast] using
      (ZMod.intCast_eq_intCast_iff_dvd_sub (n : ℤ) (m : ℤ) q).mpr hqdiv
  exact (ZMod.natCast_eq_natCast_iff' n m q).mp heq

/-- Cardinality comparison for two finite images when one map refines the other. -/
theorem image_card_le_of_refines {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (A : Finset α) (f : α→β) (g : α→γ)
    (href : ∀x∈A,∀y∈A,g x=g y→f x=f y) :
    (A.image f).card≤(A.image g).card := by
  classical
  have hex (z : A.image f) : ∃x, x∈A ∧ f x=z.val := Finset.mem_image.mp z.property
  let pick (z : A.image f) : α := Classical.choose (hex z)
  have hpick (z : A.image f) : pick z∈A ∧ f (pick z)=z.val :=
    Classical.choose_spec (hex z)
  apply Finset.card_le_card_of_injective (f := fun z : A.image f =>
    (⟨g (pick z),Finset.mem_image_of_mem g (hpick z).1⟩ : A.image g))
  intro z w hzw
  apply Subtype.ext
  exact (hpick z).2.symm.trans
    ((href _ (hpick z).1 _ (hpick w).1 (congrArg Subtype.val hzw)).trans (hpick w).2)

/-- Actual quotient residue classes inject into the actual unity root set. -/
theorem quotient_residue_card_le_unity (d : ℕ) (A : Finset ℕ)
    {q l : ℕ} (hq : 0<q) (hl : 0<l)
    (hcop : ∀n∈A,Nat.Coprime n (l*q))
    (hdiv : ∀n∈A,(q : ℤ)∣differenceQuotient d n l) :
    (A.image (fun n=>n%q)).card≤(unityRoots d (l*q)).card := by
  letI : NeZero (l*q) := ⟨(Nat.mul_pos hl hq).ne'⟩
  have href : ∀n∈A,∀m∈A,(ratio q l n).val=(ratio q l m).val→n%q=m%q := by
    intro n hn m hm h
    apply ratio_eq_implies_mod_eq hl (hcop n hn) (hcop m hm)
    exact ZMod.val_injective _ h
  have hsub : A.image (fun n=>(ratio q l n).val)⊆unityRoots d (l*q) := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hx
    apply mem_unityRoots.mpr
    refine ⟨(ratio q l n).val_lt,?_⟩
    rw [ZMod.natCast_zmod_val]
    exact ratio_pow_eq_one (hcop n hn) (hdiv n hn)
  exact (image_card_le_of_refines A (fun n=>n%q) (fun n=>(ratio q l n).val) href).trans
    (Finset.card_le_card hsub)

/-- An interval contains at most N/q+1 representatives of each residue. -/
theorem interval_card_le_residues (A : Finset ℕ) {q N : ℕ} (hq : 0<q)
    (hA : A⊆Finset.Icc 1 N) :
    A.card≤(A.image (fun n=>n%q)).card*(N/q+1) := by
  classical
  have hc : A.card≤((A.image (fun n=>n%q))×ˢFinset.range (N/q+1)).card := by
    apply Finset.card_le_card_of_injOn (fun n=>(n%q,n/q))
    · intro n hn
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_image_of_mem _ hn,?_⟩
      apply Finset.mem_range.mpr
      change n/q<N/q+1
      have hh : n/q≤N/q := Nat.div_le_div_right (Finset.mem_Icc.mp (hA hn)).2
      omega
    · intro n hn m hm hnm
      have hmod := congrArg Prod.fst hnm
      have hdiv := congrArg Prod.snd hnm
      change n%q=m%q at hmod
      change n/q=m/q at hdiv
      calc
        n=n%q+q*(n/q) := (Nat.mod_add_div n q).symm
        _ = m%q+q*(m/q) := by rw [hmod,hdiv]
        _ = m := Nat.mod_add_div m q
  simpa only [Finset.card_product,Finset.card_range] using hc

/-- The finite source domain after extracting gcd(m1,m2). -/
def quotientPoints (d q l N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n =>
    Nat.Coprime n (n+l) ∧ Nat.Coprime (n*(n+l)) q ∧
      (q : ℤ)∣differenceQuotient d n l

/-- The actual residue and interval bound needed in VW95 (4.9). -/
theorem quotientPoints_card_le {d q l N : ℕ} (hd : 0<d) (hq : 0<q) (hl : 0<l) :
    (quotientPoints d q l N).card≤(N/q+1)*(l*q).divisors.card^(2*d) := by
  have hcop : ∀n∈quotientPoints d q l N,Nat.Coprime n (l*q) := by
    intro n hn
    obtain ⟨_,hnl,hnq,_⟩ := Finset.mem_filter.mp hn
    exact (Nat.coprime_self_add_right.mp hnl).mul_right
      (Nat.coprime_mul_iff_left.mp hnq).1
  have hdiv : ∀n∈quotientPoints d q l N,(q : ℤ)∣differenceQuotient d n l :=
    fun n hn => (Finset.mem_filter.mp hn).2.2.2
  calc
    _ ≤ ((quotientPoints d q l N).image (fun n=>n%q)).card*(N/q+1) :=
      interval_card_le_residues _ hq (Finset.filter_subset _ _)
    _ ≤ (unityRoots d (l*q)).card*(N/q+1) :=
      Nat.mul_le_mul_right _ (quotient_residue_card_le_unity d _ hq hl hcop hdiv)
    _ ≤ (l*q).divisors.card^(2*d)*(N/q+1) :=
      Nat.mul_le_mul_right _ (unityRoots_card_le_divisor_power hd (Nat.mul_pos hl hq))
    _ = _ := Nat.mul_comm _ _

/-- Uniform arbitrary small power loss, with exact original integer intervals. -/
theorem quotientPoints_card_le_rpow {d : ℕ} (hd : 0<d) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀q l N : ℕ,0<q→0<l→
      ((quotientPoints d q l N).card : ℝ)≤
        C*((N : ℝ)/q+1)*((l*q : ℕ) : ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := AuxiliaryL2Grouping.divisor_power_le_rpow (2*d) hε
  refine ⟨C,hC,?_⟩
  intro q l N hq hl
  have hqR : (0 : ℝ)<q := by exact_mod_cast hq
  have hcast : ((N/q : ℕ) : ℝ)≤(N : ℝ)/q := by
    apply (le_div_iff₀ hqR).mpr
    exact_mod_cast Nat.div_mul_le_self N q
  calc
    _ ≤ ((N/q : ℕ)+1 : ℝ)*((l*q).divisors.card : ℝ)^(2*d) := by
      exact_mod_cast quotientPoints_card_le hd hq hl (N := N)
    _ ≤ ((N : ℝ)/q+1)*(C*((l*q : ℕ) : ℝ)^ε) := by
      apply mul_le_mul
      · exact add_le_add_right hcast _
      · exact hdiv _ (Nat.mul_pos hl hq)
      · positivity
      · positivity
    _ = _ := by ring

#print axioms ratio_eq_implies_mod_eq
#print axioms quotientPoints_card_le_rpow
end Waring.PolicyCompletionBinomialRoots
