import WaringSiegel.WSL4ArchLocalAffine
import WaringSiegel.WSL4ArchLocalPrime
import WaringSiegel.WSL4ArchLocalGoodAll
import WaringSiegel.MainTargets
import WaringSiegel.VerifiedThresholdTable
import Mathlib.NumberTheory.Padics.RingHoms

noncomputable section
open scoped NumberField
open Polynomial IsLocalRing

namespace WaringSmallK.Local

theorem fifth_local {K : Type*} [Field K] [NumberField K] {a : 𝓞 K}
    (ha : WaringSiegel.Eligible 5 a) : WaringSiegel.LocalUnitSolvable 5 10 a :=
  WaringSiegel.WSL4.eligible_odd_prime_localUnitSolvable 5 (by decide) (by decide) ha

theorem seventh_local {K : Type*} [Field K] [NumberField K] {a : 𝓞 K}
    (ha : WaringSiegel.Eligible 7 a) : WaringSiegel.LocalUnitSolvable 7 14 a :=
  WaringSiegel.WSL4.eligible_odd_prime_localUnitSolvable 7 (by decide) (by decide) ha

/-- In every complete local ring of residue characteristic two,
every element of 1+16A has an actual unit fourth root in 1+4A. -/
theorem quartic_lift {A : Type*} [CommRing A] [Nontrivial A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [CharP (ResidueField A) 2] (a : A) :
    ∃ t : A, (1+4*t)^4=1+16*a ∧ IsUnit (1+4*t) := by
  let F : ℤ[X] := X + 2*(3*X^2+8*X^3+8*X^4)
  have hF : F.map (Int.castRingHom (ZMod 2))=X+C 0 := by
    simp [F, Polynomial.map_ofNat, show (2 : (ZMod 2)[X]) = 0 from CharP.cast_eq_zero _ 2]
  obtain ⟨t,ht⟩ := WaringSiegel.WSL4.integer_polynomial_surjective_of_affine_mod_prime
    2 F 0 hF a
  have ht' : t+2*(3*t^2+8*t^3+8*t^4)=a := by simpa [F] using ht
  refine ⟨t,?_,?_⟩
  · rw [←ht']; ring
  · apply (residue_ne_zero_iff_isUnit _).mp
    have h4 : (4 : ResidueField A) = 0 := by
      have h2 := CharP.cast_eq_zero (ResidueField A) 2
      norm_num at h2 ⊢
      linear_combination 2*h2
    simp only [map_add, map_one, map_mul, map_ofNat, h4, zero_mul, add_zero]
    exact one_ne_zero

/-- Every 2-adic integer is the sum of one unit fourth power and
r copies of 1^4, with r at most fifteen. -/
theorem two_adic_sixteen (a : ℤ_[2]) :
    ∃ t : ℤ_[2], ∃ r : Fin 16, IsUnit (1+4*t) ∧ (1+4*t)^4+(r.val : ℤ_[2])=a := by
  letI : CharP (ResidueField ℤ_[2]) 2 :=
    charP_of_injective_ringHom (f := ((PadicInt.residueField (p:=2)).symm).toRingHom)
      (PadicInt.residueField (p:=2)).symm.injective 2
  let r : ZMod 16 := PadicInt.toZModPow 4 (a-1)
  have he : PadicInt.toZModPow 4 (a-1-(r.val : ℤ_[2]))=0 := by
    rw [map_sub, map_natCast]
    exact sub_eq_zero.mpr (ZMod.natCast_zmod_val r).symm
  have hm : a-1-(r.val : ℤ_[2]) ∈ Ideal.span {(2:ℤ_[2])^4} := by
    have hh : a-1-(r.val : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow 4) := he
    rw [PadicInt.ker_toZModPow] at hh
    exact hh
  obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp hm
  obtain ⟨t,ht,hu⟩ := quartic_lift c
  refine ⟨t,⟨r.val,r.val_lt⟩,hu,?_⟩
  rw [ht]; dsimp
  linear_combination -hc

/-- The zero target has no primitive representation by at most fifteen fourth powers
over the two-adic integers. -/
theorem two_adic_lower {s : ℕ} (hs : s < 16) (x : Fin s → ℤ_[2])
    (hu : ∃ i, IsUnit (x i)) : (∑ i, (x i)^4) ≠ 0 := by
  classical
  let f : ℤ_[2] →+* ZMod 16 := PadicInt.toZModPow 4
  let B := Finset.univ.filter (fun i => (f (x i))^4 = 1)
  have values : ∀ a : ZMod 16, a^4 = 0 ∨ a^4 = 1 := by decide
  have units : ∀ a : ZMod 16, IsUnit a → a^4 = 1 := by decide
  obtain ⟨j,hj⟩ := hu
  have hjB : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,units _ (hj.map f)⟩
  have hpos : 0 < B.card := Finset.card_pos.mpr ⟨j,hjB⟩
  have hlt : B.card < 16 := lt_of_le_of_lt (le_trans (Finset.card_filter_le _ _) (by simp)) hs
  have hcount : (∑ i, (f (x i))^4) = (B.card : ZMod 16) := by
    calc
      _ = ∑ i : Fin s, (if (f (x i))^4 = 1 then 1 else 0 : ZMod 16) := by
        apply Finset.sum_congr rfl
        intro i _
        rcases values (f (x i)) with h|h <;> simp [h]
      _ = _ := by simp [B,Finset.sum_boole]
  intro h
  have hh := congrArg f h
  simp only [map_sum, map_pow, map_zero] at hh
  have hd : 16 ∣ B.card := (ZMod.natCast_eq_zero_iff _ _).mp (hcount.symm.trans hh)
  omega

theorem two_adic_tuple (a : ℤ_[2]) :
    ∃ x : Fin 16 → ℤ_[2], (∑ i, (x i)^4) = a ∧ ∃ i, IsUnit (x i) := by
  obtain ⟨t,r,hu,h⟩ := two_adic_sixteen a
  let x : Fin (r.val+1) → ℤ_[2] := Fin.cons (1+4*t) (fun _ => 1)
  have hx : (∑ i, (x i)^4) = a := by simpa [x,Fin.sum_univ_succ] using h
  exact WaringSiegel.WSL4.power_tuple_with_unit_mono 4 (by decide)
    ⟨x,hx,0,hu⟩ (by have := r.isLt; omega)

/-- The completion hypothesis holds when 2 splits completely. -/
def DyadicCompletionsAreZ2 (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    ¬ IsUnit (4:v.adicCompletionIntegers K) →
      Nonempty (v.adicCompletionIntegers K ≃+* ℤ_[2])

theorem split_dyadic_quartic_local {K : Type*} [Field K] [NumberField K]
    (hs : DyadicCompletionsAreZ2 K) {a : 𝓞 K} (ha : WaringSiegel.Eligible 4 a) :
    WaringSiegel.LocalUnitSolvable 4 16 a := by
  intro v
  by_cases h4 : IsUnit (4:v.adicCompletionIntegers K)
  · exact WaringSiegel.WSL4.power_tuple_with_unit_mono 4 (by decide)
      (WaringSiegel.WSL4.power_tuple_in_completion_of_unit v 4 (by decide) h4 ha) (by decide)
  · obtain ⟨e⟩ := hs v h4
    let b := algebraMap (𝓞 K) (v.adicCompletionIntegers K) a
    obtain ⟨x,hx,i,hi⟩ := two_adic_tuple (e b)
    refine ⟨fun j => e.symm (x j),?_,i,hi.map e.symm.toRingHom⟩
    apply e.injective
    simpa only [map_sum,map_pow,RingEquiv.apply_symm_apply] using hx

theorem split_dyadic_quartic_of_largeK (hA : WaringSiegel.LargeKAnalyticClaim)
    (K : Type) [Field K] [NumberField K] (h : DyadicCompletionsAreZ2 K) :
    WaringSiegel.WaringSiegelBound K 4 16 := by
  apply WaringSiegel.bound_of_localConditionalBound (hA K 4 16 (by decide) ?_)
  · exact fun _ ha => split_dyadic_quartic_local h ha
  · rw [WaringSiegel.Thresholds.variables_4]; decide

/-- Fourth powers give all residue digits when the maximal ideal is generated by 2. -/
theorem fourth_digit {A : Type*} [CommRing A] [Nontrivial A] [IsLocalRing A]
    [Finite (ResidueField A)] [CharP (ResidueField A) 2]
    (he : maximalIdeal A = Ideal.span {(2:A)}) (a : A) :
    ∃ x c : A, a = x^4+2*c := by
  obtain ⟨v,hv⟩ := surjective_frobenius (ResidueField A) 2 (residue A a)
  obtain ⟨u,hu⟩ := surjective_frobenius (ResidueField A) 2 v
  obtain ⟨x,hx⟩ := residue_surjective (R:=A) u
  change v^2 = residue A a at hv
  change u^2 = v at hu
  have hz : residue A (a-x^4)=0 := by
    rw [map_sub,map_pow,hx, ←hv, ←hu]
    ring
  have hp := (residue_eq_zero_iff _).mp hz
  rw [he,Ideal.mem_span_singleton] at hp
  obtain ⟨c,hc⟩ := hp
  exact ⟨x,c,by linear_combination hc⟩

theorem unramified_quartic_tuple {A : Type*} [CommRing A] [Nontrivial A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)] [CharP (ResidueField A) 2]
    (he : maximalIdeal A = Ideal.span {(2:A)}) (a : A) :
    ∃ x : Fin 16 → A, (∑ i, (x i)^4) = a ∧ ∃ i, IsUnit (x i) := by
  obtain ⟨w,b,hw⟩ := fourth_digit he (a-1)
  obtain ⟨x,c,hx⟩ := fourth_digit he b
  obtain ⟨y,d,hy⟩ := fourth_digit he c
  obtain ⟨z,e,hz⟩ := fourth_digit he d
  obtain ⟨t,ht,hu⟩ := quartic_lift e
  let l := [1+4*t,w,x,x,y,y,y,y,z,z,z,z,z,z,z,z]
  refine ⟨l.get,?_,(0 : Fin 16),hu⟩
  change (∑ i : Fin l.length, (l.get i)^4) = a
  rw [WaringSiegel.WSL4.sum_power_get_eq_localPowerListSum]
  simp only [l,WaringSiegel.WSL4.localPowerListSum,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,ht]
  linear_combination -hw - 2*hx - 4*hy - 8*hz

/-- At every dyadic place, the maximal ideal is generated by the rational prime 2. -/
def UnramifiedAtTwo (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ¬ IsUnit (4:v.adicCompletionIntegers K) →
    maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {(2:v.adicCompletionIntegers K)}

theorem unramified_quartic_local {K : Type*} [Field K] [NumberField K]
    (hs : UnramifiedAtTwo K) {a : 𝓞 K} (ha : WaringSiegel.Eligible 4 a) :
    WaringSiegel.LocalUnitSolvable 4 16 a := by
  intro v
  by_cases h4 : IsUnit (4:v.adicCompletionIntegers K)
  · exact WaringSiegel.WSL4.power_tuple_with_unit_mono 4 (by decide)
      (WaringSiegel.WSL4.power_tuple_in_completion_of_unit v 4 (by decide) h4 ha) (by decide)
  · let A := v.adicCompletionIntegers K
    have h2 : ¬IsUnit (2:A) := fun h => h4 (by convert h.mul h using 1; norm_num)
    letI := WaringSiegel.WSL4.residue_charP_of_prime_not_isUnit 2 (by decide) h2
    letI := WaringSiegel.completionIntegers_residueFinite v
    letI := WaringSiegel.completionIntegers_isAdicComplete v
    exact unramified_quartic_tuple (hs v h4) _

theorem unramified_quartic_of_largeK (hA : WaringSiegel.LargeKAnalyticClaim)
    (K : Type) [Field K] [NumberField K] (h : UnramifiedAtTwo K) :
    WaringSiegel.WaringSiegelBound K 4 16 := by
  apply WaringSiegel.bound_of_localConditionalBound (hA K 4 16 (by decide) ?_)
  · exact fun _ ha => unramified_quartic_local h ha
  · rw [WaringSiegel.Thresholds.variables_4]; decide

end WaringSmallK.Local
#print axioms WaringSmallK.Local.unramified_quartic_local
#print axioms WaringSmallK.Local.unramified_quartic_of_largeK
#print axioms WaringSmallK.Local.split_dyadic_quartic_of_largeK
#print axioms WaringSmallK.Local.split_dyadic_quartic_local
#print axioms WaringSmallK.Local.two_adic_tuple
#print axioms WaringSmallK.Local.two_adic_lower
#print axioms WaringSmallK.Local.fifth_local
#print axioms WaringSmallK.Local.seventh_local
#print axioms WaringSmallK.Local.quartic_lift
#print axioms WaringSmallK.Local.two_adic_sixteen
