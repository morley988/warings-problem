import Waring.PolicyCompletionHolder
import Waring.PolicyCompletionSmoothDecomposition

/-!
# Finite good-block reduction in efficient differencing

Every original good smooth tuple is covered by an actual tuple of smooth
block divisors and shorter smooth quotients. The resulting enlarged family
is grouped by its coefficient tuple with finite Cauchy. The homogeneous
moment reduction then gives the exact factor `#W^(2s-1)`.
-/

noncomputable section
open scoped BigOperators

namespace Waring.PolicyCompletionGoodBlocks
open AuxiliaryL2Grouping PolicyCompletionHolder SmoothMoments

/-- A frequency-preserving finite cover cannot reduce the collision count. -/
theorem collision_card_le_of_cover {α β : Type*}
    (A : Finset α) (B : Finset β) (restore : β → α)
    (f : α → ℤ) (g : β → ℤ)
    (hcover : ∀ x ∈ A, ∃ y ∈ B, restore y=x)
    (hfreq : ∀ y ∈ B, g y=f (restore y)) :
    (collisionPairs A f).card ≤ (collisionPairs B g).card := by
  classical
  apply Finset.card_le_card_of_surjOn (fun p : β × β => (restore p.1,restore p.2))
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp,heq⟩
  rcases Finset.mem_product.mp hp with ⟨hx,hy⟩
  obtain ⟨x,hxB,hxR⟩ := hcover p.1 hx
  obtain ⟨y,hyB,hyR⟩ := hcover p.2 hy
  refine ⟨(x,y),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxB,hyB⟩,?_⟩,?_⟩
  · rw [hfreq x hxB,hfreq y hyB,hxR,hyR]
    exact heq
  · exact Prod.ext hxR hyR

def blockDomain {α γ : Type*} {s : ℕ} (A : Finset α) (good : γ → α → Prop)
    (w : Fin s → γ) : Finset α := by
  classical
  exact A.filter (fun a => ∀ i, good (w i) a)

def singleBlockDomain {α γ : Type*} (A : Finset α) (good : γ → α → Prop)
    (w : γ) : Finset α := by
  classical
  exact A.filter (good w)

def blockEndpoints {α β γ : Type*} (s : ℕ) (W : Finset γ) (A : Finset α)
    (B : Finset β) (good : γ → α → Prop) : Finset ((Fin s → γ) × (α × (Fin s → β))) := by
  classical
  exact ((finiteTuples W s) ×ˢ (A ×ˢ finiteTuples B s)).filter
    (fun x => ∀ i, good (x.1 i) x.2.1)

def blockFrequency {α β γ : Type*} {s : ℕ} (f : α → ℤ) (g : γ → β → ℤ)
    (x : (Fin s → γ) × (α × (Fin s → β))) : ℤ :=
  f x.2.1+∑ i, g (x.1 i) (x.2.2 i)

/-- Fixing the coefficient tuple preserves the exact heterogeneous frequency
and projects injectively to the corresponding tuple collision set. -/
theorem class_collision_card_le_tuple {α β γ : Type*} [DecidableEq γ]
    (s : ℕ) (W : Finset γ) (A : Finset α) (B : Finset β)
    (good : γ → α → Prop) (f : α → ℤ) (g : γ → β → ℤ) (w : Fin s → γ) :
    (collisionPairs (classFiber (blockEndpoints s W A B good) Prod.fst w)
      (blockFrequency f g)).card ≤
      (tupleCollision s (blockDomain A good w) B f (fun i => g (w i))).card := by
  classical
  have hkeys {x : (Fin s → γ) × (α × (Fin s → β))}
      (hx : x ∈ classFiber (blockEndpoints s W A B good) Prod.fst w) :
      x.1=w ∧ x.2.1 ∈ blockDomain A good w ∧ x.2.2 ∈ finiteTuples B s := by
    rcases Finset.mem_filter.mp hx with ⟨hx,hkey⟩
    rcases Finset.mem_filter.mp hx with ⟨hx,hgood⟩
    have hAB := (Finset.mem_product.mp hx).2
    refine ⟨hkey,Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hAB).1,?_⟩,
      (Finset.mem_product.mp hAB).2⟩
    simpa only [hkey] using hgood
  apply Finset.card_le_card_of_injOn
    (fun p : ((Fin s → γ) × (α × (Fin s → β))) ×
      ((Fin s → γ) × (α × (Fin s → β))) => (p.1.2,p.2.2))
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp,hfreq⟩
    have hl := hkeys (Finset.mem_product.mp hp).1
    have hr := hkeys (Finset.mem_product.mp hp).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr hl.2,
      Finset.mem_product.mpr hr.2⟩,?_⟩
    simpa only [blockFrequency,tupleFrequency,hl.1,hr.1] using hfreq
  · intro p hp q hq heq
    have hpl := hkeys (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hpr := hkeys (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
    have hql := hkeys (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    have hqr := hkeys (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
    have hl : p.1.2=q.1.2 := congrArg
      (fun v : (α × (Fin s → β)) × (α × (Fin s → β)) => v.1) heq
    have hr : p.2.2=q.2.2 := congrArg
      (fun v : (α × (Fin s → β)) × (α × (Fin s → β)) => v.2) heq
    exact Prod.ext (Prod.ext (hpl.1.trans hql.1.symm) hl)
      (Prod.ext (hpr.1.trans hqr.1.symm) hr)

/-- Complete Cauchy/AM--GM good-block reduction with the source's exact
coefficient exponent. No source moment estimate is assumed. -/
theorem block_collisions_le_homogeneous {α β γ : Type*} [DecidableEq γ]
    {s : ℕ} (hs : 0 < s) (W : Finset γ) (A : Finset α) (B : Finset β)
    (good : γ → α → Prop) (f : α → ℤ) (g : γ → β → ℤ) :
    ((collisionPairs (blockEndpoints s W A B good) (blockFrequency f g)).card : ℝ) ≤
      (W.card : ℝ)^(2*s-1) * ∑ w ∈ W,
        mixedFrequencyEvenMoment (singleBlockDomain A good w) f 1 B (g w) s := by
  classical
  let E := blockEndpoints s W A B good
  let WT := finiteTuples W s
  have hkey : ∀ x ∈ E, x.1 ∈ WT :=
    fun x hx => (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  have hgroup := collision_card_le_classes E (blockFrequency f g) Prod.fst WT hkey
    (D := (WT.card : ℝ)) (by positivity) (by
      intro n hn
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro w hw
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
      exact hkey x (Finset.mem_filter.mp hx).1)
  have hclasses : (∑ w ∈ WT,
      ((collisionPairs (classFiber E Prod.fst w) (blockFrequency f g)).card : ℝ)) ≤
      ∑ w ∈ WT, ((tupleCollision s (blockDomain A good w) B f (fun i => g (w i))).card : ℝ) := by
    apply Finset.sum_le_sum
    intro w hw
    exact_mod_cast class_collision_card_le_tuple s W A B good f g w
  have hsum := sum_tupleCollision_le_homogeneous hs W (blockDomain A good)
    (singleBlockDomain A good) B f g (by
      intro w hw i a ha
      rcases Finset.mem_filter.mp ha with ⟨ha,hgood⟩
      exact Finset.mem_filter.mpr ⟨ha,hgood i⟩)
  have hWT : (WT.card : ℝ)=(W.card : ℝ)^s := by
    simp [WT,finiteTuples,Fintype.card_piFinset]
  calc
    _ ≤ (WT.card : ℝ) * ∑ w ∈ WT,
        ((collisionPairs (classFiber E Prod.fst w) (blockFrequency f g)).card : ℝ) := hgroup
    _ ≤ (WT.card : ℝ) * ((W.card : ℝ)^(s-1) *
        ∑ w ∈ W, mixedFrequencyEvenMoment (singleBlockDomain A good w) f 1 B (g w) s) :=
      mul_le_mul_of_nonneg_left (hclasses.trans hsum) (by positivity)
    _ = _ := by
      rw [hWT,← mul_assoc,← pow_add]
      congr 2
      omega

/-- Every chosen block divisor leaves a shorter positive smooth quotient. -/
theorem exists_short_smooth_quotient {n d : ℕ} {P R M : ℝ}
    (hP : 0 ≤ P) (hM : 1 ≤ M) (hn : n ∈ smoothNumbers P R)
    (hdn : d ∣ n) (hMd : M < (d : ℝ)) :
    ∃ u : ℕ, n=d*u ∧ u ∈ smoothNumbers (P/M) R := by
  obtain ⟨⟨hnpos,hnP⟩,hsmooth⟩ := mem_smoothNumbers.mp hn
  obtain ⟨u,hnu⟩ := hdn
  have hupos : 0 < u := by
    by_contra hu
    have hu0 : u=0 := by omega
    simp only [hu0,mul_zero] at hnu
    omega
  have huR : (0 : ℝ) < u := by exact_mod_cast hupos
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hnR : (n : ℝ) ≤ P :=
    (by exact_mod_cast hnP : (n : ℝ) ≤ ⌊P⌋₊).trans (Nat.floor_le hP)
  have hprod : (n : ℝ)=(d : ℝ)*(u : ℝ) := by exact_mod_cast hnu
  have huPM : (u : ℝ) < P/M := by
    apply (lt_div_iff₀ hMpos).mpr
    calc
      (u : ℝ)*M = M*(u : ℝ) := mul_comm _ _
      _ < (d : ℝ)*(u : ℝ) := mul_lt_mul_of_pos_right hMd huR
      _ = (n : ℝ) := hprod.symm
      _ ≤ P := hnR
  refine ⟨u,hnu,mem_smoothNumbers.mpr ⟨⟨by omega,Nat.le_floor huPM.le⟩,?_⟩⟩
  exact hsmooth.of_dvd ⟨d,by rw [hnu,mul_comm]⟩

/-- Original good endpoints, with every smooth variable admitting an actual
coprime block divisor for its own polynomial parameter. -/
def goodSmoothEndpoints {α : Type*} (s : ℕ) (A : Finset α)
    (P R M : ℝ) (D : α → ℕ) : Finset (α × (Fin s → ℕ)) := by
  classical
  exact (A ×ˢ finiteTuples (smoothNumbers P R) s).filter (fun x =>
    ∀ i, ∃ d : ℕ, d ∈ CoefficientPower.coefficientBlock P R M ∧
      d ∣ x.2 i ∧ d.Coprime (D x.1))

def restoreSmoothEndpoint {α : Type*} {s : ℕ}
    (x : (Fin s → ℕ) × (α × (Fin s → ℕ))) : α × (Fin s → ℕ) :=
  (x.2.1,fun i => x.1 i*x.2.2 i)

/-- The short-quotient block family covers every actual good smooth tuple. -/
theorem goodSmoothEndpoints_covered {α : Type*} (s : ℕ) (A : Finset α)
    {P R M : ℝ} (hP : 0 ≤ P) (hM : 1 ≤ M) (D : α → ℕ) :
    ∀ x ∈ goodSmoothEndpoints s A P R M D,
      ∃ y ∈ blockEndpoints s (CoefficientPower.coefficientBlock P R M) A
        (smoothNumbers (P/M) R) (fun d a => d.Coprime (D a)),
        restoreSmoothEndpoint y=x := by
  classical
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hx,hgood⟩
  rcases Finset.mem_product.mp hx with ⟨hxA,hxtuple⟩
  have hfact (i : Fin s) : ∃ d u : ℕ,
      x.2 i=d*u ∧ d ∈ CoefficientPower.coefficientBlock P R M ∧
      u ∈ smoothNumbers (P/M) R ∧ d.Coprime (D x.1) := by
    obtain ⟨d,hd,hdn,hcop⟩ := hgood i
    have hni : x.2 i ∈ smoothNumbers P R := Fintype.mem_piFinset.mp hxtuple i
    have hMd : M < (d : ℝ) := (Finset.mem_filter.mp hd).2.1
    obtain ⟨u,hnu,hu⟩ := exists_short_smooth_quotient hP hM hni hdn hMd
    exact ⟨d,u,hnu,hd,hu,hcop⟩
  choose w u hprod hw hu hcop using hfact
  refine ⟨(w,(x.1,u)),?_,?_⟩
  · simp only [blockEndpoints,Finset.mem_filter,Finset.mem_product]
    exact ⟨⟨Fintype.mem_piFinset.mpr hw,hxA,Fintype.mem_piFinset.mpr hu⟩,hcop⟩
  · change (x.1,fun i => w i*u i)=x
    exact Prod.ext rfl (funext (fun i => (hprod i).symm))

/-- The genuine all-good smooth collision count satisfies the homogeneous
block estimate required in the fundamental efficient-differencing lemma. -/
theorem goodSmooth_collisions_le_homogeneous {α : Type*}
    {s : ℕ} (hs : 0 < s) (k : ℕ) (A : Finset α) (f : α → ℤ)
    {P R M : ℝ} (hP : 0 ≤ P) (hM : 1 ≤ M) (D : α → ℕ) :
    ((collisionPairs (goodSmoothEndpoints s A P R M D)
      (tupleFrequency f (fun _ n => ((n^k : ℕ) : ℤ)))).card : ℝ) ≤
      ((CoefficientPower.coefficientBlock P R M).card : ℝ)^(2*s-1) *
        ∑ w ∈ CoefficientPower.coefficientBlock P R M,
          mixedFrequencyEvenMoment (singleBlockDomain A (fun d a => d.Coprime (D a)) w)
            f 1 (smoothNumbers (P/M) R) (fun u => (w : ℤ)^k*(u : ℤ)^k) s := by
  let W := CoefficientPower.coefficientBlock P R M
  let B := smoothNumbers (P/M) R
  let good := fun d a => Nat.Coprime d (D a)
  have hcover := collision_card_le_of_cover (goodSmoothEndpoints s A P R M D)
    (blockEndpoints s W A B good) restoreSmoothEndpoint
    (tupleFrequency f (fun _ n => ((n^k : ℕ) : ℤ)))
    (blockFrequency f (fun w u => (w : ℤ)^k*(u : ℤ)^k))
    (goodSmoothEndpoints_covered s A hP hM D) (by
      intro y hy
      simp only [blockFrequency,tupleFrequency,restoreSmoothEndpoint,Nat.cast_pow,Nat.cast_mul,mul_pow])
  exact (by exact_mod_cast hcover :
      ((collisionPairs (goodSmoothEndpoints s A P R M D)
        (tupleFrequency f (fun _ n => ((n^k : ℕ) : ℤ)))).card : ℝ) ≤
      ((collisionPairs (blockEndpoints s W A B good)
        (blockFrequency f (fun w u => (w : ℤ)^k*(u : ℤ)^k))).card : ℝ)).trans
    (block_collisions_le_homogeneous hs W A B good f (fun w u => (w : ℤ)^k*(u : ℤ)^k))

#print axioms collision_card_le_of_cover
#print axioms block_collisions_le_homogeneous
#print axioms goodSmoothEndpoints_covered
#print axioms goodSmooth_collisions_le_homogeneous

end Waring.PolicyCompletionGoodBlocks
