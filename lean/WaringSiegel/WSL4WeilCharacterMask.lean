import WaringSiegel.WSL4WeilRingCharacters
import WaringSiegel.WSL3PoissonCoprimeWeyl

/-! # Exact unit-mask transfer for finite quotient characters

All twists here are characters of the actual finite quotient.  Character
averaging costs one for imposing an ideal and at most two for avoiding it.
-/
noncomputable section
namespace WaringSiegel.WSL4Weil
open scoped BigOperators Classical NumberField
open WSL3Poisson NumberField Module

def finiteLinearCharSum {A : Type*} [AddCommGroup A]
    (S : Finset A) (F : A→ℂ) (χ : AddChar A ℂ) : ℂ := ∑x∈S,F x*χ x

theorem finiteLinearCharSum_zero_fiber_bound
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B]
    (S : Finset A) (F : A→ℂ) (D : ℝ)
    (hD : ∀χ : AddChar A ℂ, ‖finiteLinearCharSum S F χ‖≤D)
    (f : A→+B) (χ : AddChar A ℂ) :
    ‖finiteLinearCharSum (S.filter (fun x=>f x=0)) F χ‖≤D := by
  let n := Fintype.card B
  have hn : 0<(n:ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  let T : AddChar B ℂ→ℂ := fun η=>∑x∈S,F x*χ x*η (f x)
  have he : (∑η,T η)=(n:ℂ)*finiteLinearCharSum (S.filter (fun x=>f x=0)) F χ := by
    dsimp only [T,finiteLinearCharSum]
    rw [Finset.sum_comm,Finset.sum_filter,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.mul_sum,AddChar.sum_apply_eq_ite]
    by_cases h : f x=0 <;> simp only [h,if_true,if_false,mul_zero,mul_one,n] <;> ring
  have hT (η : AddChar B ℂ) : ‖T η‖≤D := by
    have h := hD (χ*(η.compAddMonoidHom f))
    simpa only [T,finiteLinearCharSum,AddChar.mul_apply,AddChar.compAddMonoidHom_apply,mul_assoc] using h
  have hb : ‖∑η,T η‖≤(n:ℝ)*D := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _η : AddChar B ℂ,D := Finset.sum_le_sum (fun η _=>hT η)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,AddChar.card_eq,n]
  rw [he,norm_mul,Complex.norm_natCast] at hb
  exact (mul_le_mul_left hn).mp hb

theorem finiteLinearCharSum_ideal_bound
    {A : Type*} [CommRing A] [Fintype A]
    (S : Finset A) (F : A→ℂ) (D : ℝ)
    (hD : ∀χ : AddChar A ℂ, ‖finiteLinearCharSum S F χ‖≤D)
    (J : Ideal A) (χ : AddChar A ℂ) :
    ‖finiteLinearCharSum (S.filter (fun x=>x∈J)) F χ‖≤D := by
  letI : Fintype (A ⧸ J) := Fintype.ofFinite _
  have h := finiteLinearCharSum_zero_fiber_bound S F D hD (Ideal.Quotient.mk J).toAddMonoidHom χ
  change ‖finiteLinearCharSum (S.filter (fun x=>Ideal.Quotient.mk J x=0)) F χ‖≤D at h
  simpa only [Ideal.Quotient.eq_zero_iff_mem] using h

theorem finiteLinearCharSum_avoid_ideals_bound
    {A : Type*} [CommRing A] [Fintype A]
    (J : Finset (Ideal A)) (S : Finset A) (F : A→ℂ) (D : ℝ)
    (hD : ∀χ : AddChar A ℂ, ‖finiteLinearCharSum S F χ‖≤D) :
    ∀χ, ‖finiteLinearCharSum (S.filter (fun x=>∀I∈J,x∉I)) F χ‖≤(2:ℝ)^J.card*D := by
  induction J using Finset.induction_on with
  | empty => simpa using hD
  | @insert I J hIJ ih =>
    let T := S.filter (fun x=>∀A∈J,x∉A)
    have he : S.filter (fun x=>∀A∈insert I J,x∉A)=T.filter (fun x=>x∉I) := by
      ext x
      simp only [T,Finset.mem_filter,Finset.mem_insert,forall_eq_or_imp]
      tauto
    intro χ
    rw [he]
    have hpart : finiteLinearCharSum (T.filter (fun x=>x∉I)) F χ=
        finiteLinearCharSum T F χ-finiteLinearCharSum (T.filter (fun x=>x∈I)) F χ := by
      apply eq_sub_iff_add_eq.mpr
      unfold finiteLinearCharSum
      rw [← Finset.sum_filter_add_sum_filter_not T (fun x=>x∈I)]
      ring
    rw [hpart]
    apply (norm_sub_le _ _).trans
    apply (add_le_add (ih χ) (finiteLinearCharSum_ideal_bound T F _ ih I χ)).trans_eq
    rw [Finset.card_insert_of_notMem hIJ,pow_succ]
    ring

variable {K : Type*} [Field K] [NumberField K]

theorem quotient_mk_mem_map_ideal_iff (M I : Ideal (𝓞 K)) (hMI : M≤I) (x : 𝓞 K) :
    Ideal.Quotient.mk M x ∈ I.map (Ideal.Quotient.mk M) ↔ x∈I := by
  rw [Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk M) Ideal.Quotient.mk_surjective]
  constructor
  · rintro ⟨y,hy,he⟩
    have hm : y-x∈M := Ideal.Quotient.eq.mp he
    have h := I.sub_mem hy (hMI hm)
    simpa only [sub_sub_cancel] using h
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem finiteLinearCharSum_coprime_prime_bound
    (M : Ideal (𝓞 K)) (hM : M≠0) (p : ℕ) (hp : p.Prime)
    (hMP : M≤Ideal.span ({(p:𝓞 K)} : Set (𝓞 K)))
    [Fintype (𝓞 K ⧸ M)] (S : Finset (𝓞 K ⧸ M)) (F : (𝓞 K ⧸ M)→ℂ) (D : ℝ)
    (hD : ∀χ : AddChar (𝓞 K ⧸ M) ℂ,‖finiteLinearCharSum S F χ‖≤D)
    (χ : AddChar (𝓞 K ⧸ M) ℂ) :
    ‖finiteLinearCharSum (S.filter (fun x=>IsUnit (Ideal.Quotient.factor hMP x))) F χ‖≤
      (2:ℝ)^finrank ℚ K*D := by
  let V := cubicAuxiliaryPrimeSet (K:=K) p hp
  let J := V.image (fun v=>v.asIdeal.map (Ideal.Quotient.mk M))
  have hMv (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hv : v∈V) : M≤v.asIdeal := by
    apply hMP.trans
    rw [Ideal.span_singleton_le_iff_mem]
    exact (mem_cubicAuxiliaryPrimeSet hp v).mp hv
  have he : S.filter (fun x=>IsUnit (Ideal.Quotient.factor hMP x))=
      S.filter (fun x=>∀I∈J,x∉I) := by
    ext x
    simp only [Finset.mem_filter]
    apply and_congr_right
    intro hx
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.factor_mk,quotient_unit_iff_avoid_auxiliary_primes p hp a]
    constructor
    · intro h I hI
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
      exact fun ha=>h v hv ((quotient_mk_mem_map_ideal_iff M v.asIdeal (hMv v hv) a).mp ha)
    · intro h v hv ha
      exact h _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
        ((quotient_mk_mem_map_ideal_iff M v.asIdeal (hMv v hv) a).mpr ha)
  rw [he]
  apply (finiteLinearCharSum_avoid_ideals_bound J S F D hD χ).trans
  have hcard : J.card≤finrank ℚ K := (Finset.card_image_le).trans
    (prime_ideals_above_rational_prime_card_le hp V
      (fun v hv=>(mem_cubicAuxiliaryPrimeSet hp v).mp hv))
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hcard)
    ((norm_nonneg _).trans (hD 1))
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.finiteLinearCharSum_zero_fiber_bound
#print axioms WaringSiegel.WSL4Weil.finiteLinearCharSum_coprime_prime_bound
