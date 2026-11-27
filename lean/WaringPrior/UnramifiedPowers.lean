import WaringSiegel.MainTargets
import WaringSiegel.WSL4MajorRamanujamHensel
import WaringSiegel.WSL4ArchLocalGoodAll
import WaringSiegel.WSL4ArchLocalPrimeHelpers
import Mathlib.FieldTheory.Perfect

noncomputable section
open scoped NumberField
open IsLocalRing WaringSiegel.WSL4

namespace WaringSmallK.UnramifiedPowers
variable {A : Type*} [CommRing A] [Nontrivial A] [IsLocalRing A]
    [Finite (ResidueField A)] [CharP (ResidueField A) 2]

theorem power_digit (r : ℕ) (he : maximalIdeal A = Ideal.span {(2:A)}) (a : A) :
    ∃ x c : A, a=x^(2^r)+2*c := by
  obtain ⟨u,hu⟩ := (bijective_iterateFrobenius (ResidueField A) 2 r).surjective (residue A a)
  obtain ⟨x,hx⟩ := residue_surjective (R:=A) u
  change u^(2^r)=residue A a at hu
  have hz : residue A (a-x^(2^r))=0 := by rw [map_sub,map_pow,hx,hu,sub_self]
  have hp := (residue_eq_zero_iff _).mp hz
  rw [he,Ideal.mem_span_singleton] at hp
  obtain ⟨c,hc⟩ := hp
  exact ⟨x,c,by linear_combination hc⟩

theorem binary_digits (r d : ℕ) (he : maximalIdeal A = Ideal.span {(2:A)}) (a : A) :
    ∃ l : List A, ∃ c : A, l.length+1=2^d ∧ a=localPowerListSum (2^r) l+(2:A)^d*c := by
  induction d generalizing a with
  | zero => exact ⟨[],a,by simp,by simp [localPowerListSum]⟩
  | succ d ih =>
    obtain ⟨x,b,hx⟩ := power_digit r he a
    obtain ⟨l,c,hlen,hl⟩ := ih b
    refine ⟨x::(l++l),c,?_,?_⟩
    · simp only [List.length_cons,List.length_append,pow_succ]
      omega
    · rw [localPowerListSum_cons,localPowerListSum_append,pow_succ,hx,hl]
      ring

/-- Primitive width ≤ 4·2^r over an unramified complete dyadic integer ring,
with arbitrary finite residue degree. -/
theorem primitive_width [IsAdicComplete (maximalIdeal A) A] (r : ℕ)
    (he : maximalIdeal A = Ideal.span {(2:A)}) (a : A) :
    ∃ x : Fin (4*2^r) → A, (∑ i, (x i)^(2^r))=a ∧ ∃ i,IsUnit (x i) := by
  obtain ⟨l,c,hlen,hl⟩ := binary_digits r (r+2) he (a-1)
  let z := 1+(2:A)^(r+2)*c
  have hd : (2:A)^(ramanujamLiftPrecision 2 r) ∣ z-(1:A)^(1*2^r) := by
    refine ⟨c,?_⟩
    simp [z,ramanujamLiftPrecision,ramanujamLiftOffset]
  obtain ⟨y,hy,_,hu⟩ := power_root_of_dvd_sharp 2 1 r (by decide)
    (by simp) 1 z isUnit_one hd
  rw [one_mul] at hy
  let x : Fin (l.length+1) → A := Fin.cons y l.get
  have hx : (∑ i, (x i)^(2^r)) = a := by
    simp only [x,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,sum_power_get_eq_localPowerListSum,hy,z]
    linear_combination -hl
  apply power_tuple_with_unit_mono (2^r) (by positivity) ⟨x,hx,0,hu⟩
  rw [hlen,pow_add]
  omega

/-- For power-of-two exponents the primitive local hypothesis is now discharged
at every finite completion, with arbitrary splitting type away from 2. -/
theorem all_finite_places {K : Type*} [Field K] [NumberField K]
    (he : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ¬ IsUnit (2:v.adicCompletionIntegers K) →
        maximalIdeal (v.adicCompletionIntegers K)=Ideal.span {(2:v.adicCompletionIntegers K)})
    (r : ℕ) {a : 𝓞 K} (ha : WaringSiegel.Eligible (2^r) a) :
    WaringSiegel.LocalUnitSolvable (2^r) (4*2^r) a := by
  intro v
  by_cases h2 : IsUnit (2:v.adicCompletionIntegers K)
  · have hk : IsUnit ((2^r:ℕ):v.adicCompletionIntegers K) := by
      simpa using h2.pow r
    have hpos : 0 < (2:ℕ)^r := by positivity
    exact power_tuple_with_unit_mono _ hpos
      (power_tuple_in_completion_of_unit v _ hpos hk ha) (by omega)
  · letI := residue_charP_of_prime_not_isUnit 2 (by decide) h2
    letI := WaringSiegel.completionIntegers_residueFinite v
    letI := WaringSiegel.completionIntegers_isAdicComplete v
    exact primitive_width r (he v h2) _

theorem global_of_analytic (hA : WaringSiegel.LargeKAnalyticClaim)
    (K : Type) [Field K] [NumberField K]
    (he : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      ¬ IsUnit (2:v.adicCompletionIntegers K) →
        maximalIdeal (v.adicCompletionIntegers K)=Ideal.span {(2:v.adicCompletionIntegers K)})
    (r s : ℕ) (hr : 3 ≤ 2^r) (hlocal : 4*2^r ≤ s)
    (hs : WaringSiegel.Thresholds.sufficientVariables (2^r) ≤ (s:ℤ)) :
    WaringSiegel.WaringSiegelBound K (2^r) s := by
  apply WaringSiegel.bound_of_localConditionalBound (hA K _ _ hr hs)
  exact fun _ ha => localUnitSolvable_mono _ (by positivity) (all_finite_places he r ha) hlocal

end WaringSmallK.UnramifiedPowers
#print axioms WaringSmallK.UnramifiedPowers.global_of_analytic
#print axioms WaringSmallK.UnramifiedPowers.all_finite_places
#print axioms WaringSmallK.UnramifiedPowers.primitive_width
