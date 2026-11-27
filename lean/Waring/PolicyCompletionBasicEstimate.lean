import Waring.PolicyCompletionBasicHeight

/-!
# The actual basic coefficient second-moment estimate

This composes the exact moment expansion, cubic geometric resummation,
gcd decomposition, binomial and linear steps, and weighted power step.
All finite counting and divisor inputs are proved. Only the explicit
numerical source ranges remain; no analytic estimate is assumed.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionBasicEstimate
open RationalHeight PolicyCompletionBasicMoment PolicyCompletionBasicBinomial
open PolicyCompletionBasicHeight

theorem basic_moment_height_bound {d : ℕ} (hd : 6≤d) {ε : ℝ} (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀(A : Finset ℕ) (N H J : ℕ) (M Y α : ℝ) (σ : ℕ→ℝ),
      0<N→0<H→0<J→A⊆Finset.Icc 1 N→1≤M→M≤N→1≤Y→Y≤M→
      (∀m∈A,M<(m : ℝ))→16*(H : ℝ)^3*Y≤J→
      2*Y^3*Real.sqrt (((H : ℝ)^3*J)*((d : ℝ)*(N : ℝ)^(d-1)))/((H : ℝ)^3*J)<1→
      2*Y^d<Real.sqrt (((H : ℝ)^3*J)*M^d)→
      basicMoment A d H J α σ≤
        C*(J : ℝ)*H*(N : ℝ)^2*(denominatorScale d N ((H : ℝ)^3*J))^ε*
          (1+Real.log (2*(N : ℝ)))^2*(1+Real.log H)*
          (1/Y+1/(height (((H : ℝ)^3*J)*M^d) α)^(2/(d : ℝ))) := by
  let δ := ε/2
  have hδ : 0<δ := by dsimp [δ]; linarith
  obtain ⟨Ch,hCh,hheight⟩ := off_diagonal_height_bound hd hδ
  obtain ⟨Cd,hCd,hdiv⟩ := DivisorBound.divisor_count_le_cutoff_rpow hδ
  refine ⟨2+2*Cd*Ch,by positivity,?_⟩
  intro A N H J M Y α σ hN hH hJ hA hM hMN hY hYM hAlower hcubic hbin hpower
  let V := (H : ℝ)^3*J
  let T := denominatorScale d N V
  let L := 1+Real.log (2*(N : ℝ))
  let Lh := 1+Real.log (H : ℝ)
  let E := 1/Y+1/(height (V*M^d) α)^(2/(d : ℝ))
  let B := (J : ℝ)*H*(N : ℝ)^2*T^ε*L^2*Lh*E
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  have hHR : (1 : ℝ)≤H := by exact_mod_cast hH
  have hJR : (1 : ℝ)≤J := by exact_mod_cast hJ
  have hYp : 0<Y := zero_lt_one.trans_le hY
  have hVp : 0<V := by dsimp [V]; positivity
  have hV : 1≤V := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hHR) hJR
  have hT : 1≤T := (denominatorScale_ge (by omega : 0<d) hN hV).1
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hVT : V≤T := by
    have hcoef : 1≤2*(d : ℝ)*(N : ℝ)^d := by
      have hdR : (1 : ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
      have hp := one_le_pow₀ (n := d) hNR
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hcoef hVp.le
    dsimp [T,denominatorScale]
    nlinarith only [hh]
  have hL : 1≤L := by
    have hh := Real.log_nonneg (show 1≤2*(N : ℝ) by linarith)
    dsimp [L]
    linarith
  have hLh : 1≤Lh := by have hh := Real.log_nonneg hHR; dsimp [Lh]; linarith
  have hEp : 0<E := by
    have hh := Real.rpow_pos_of_pos (height_pos (V*M^d) α) (2/(d : ℝ))
    dsimp [E]
    positivity
  have hBp : 0<B := by dsimp [B]; positivity
  obtain ⟨r,hden,hreduction⟩ := basicMoment_cubic_reduction A d H J α σ hH hJ hYp hcubic
  have htau (p : ℕ×ℕ) : ((r p).den.divisors.card : ℝ)≤Cd*T^δ := by
    apply hdiv T hT _ (r p).pos
    calc
      _ ≤ Real.sqrt (V/Y) := hden p
      _ ≤ Real.sqrt V := Real.sqrt_le_sqrt (div_le_self hVp.le hY)
      _ ≤ V := by
        have hs := Real.sq_sqrt hVp.le
        have hs0 := Real.sqrt_nonneg V
        nlinarith [sq_nonneg (V-1)]
      _ ≤ T := hVT
  have hweighted :
      (∑p∈offPairs A,((r p).den.divisors.card : ℝ)/(height V (α*pairDifference d p))^(1/3 : ℝ))≤
        (Cd*T^δ)*∑p∈offPairs A,1/(height V (α*pairDifference d p))^(1/3 : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hh := height_pos V (α*pairDifference d p)
    simpa only [mul_one_div] using
      div_le_div_of_nonneg_right (htau p) (Real.rpow_pos_of_pos hh _).le
  have hheightBound := hheight A N M V Y α hN hA hM hMN hV hYp hYM hAlower hbin hpower
  have hcardNat : A.card≤N := by simpa using Finset.card_le_card hA
  have hcard : (A.card : ℝ)≤N := by exact_mod_cast hcardNat
  have hoffNat : (offPairs A).card≤N^2 := by
    calc
      _ ≤ (A×ˢA).card := Finset.card_filter_le _ _
      _ = A.card*A.card := Finset.card_product _ _
      _ ≤ N*N := Nat.mul_le_mul hcardNat hcardNat
      _ = _ := by ring
  have hoff : ((offPairs A).card : ℝ)≤(N : ℝ)^2 := by exact_mod_cast hoffNat
  have hNdiv : (N : ℝ)≤(N : ℝ)^2/Y := by
    apply (le_div_iff₀ hYp).mpr
    have hh := mul_le_mul_of_nonneg_left (hYM.trans hMN) (show (0 : ℝ)≤N by positivity)
    nlinarith only [hh]
  have hdiag : (J : ℝ)*H*A.card+(J : ℝ)*H*(offPairs A).card/Y≤
      2*(J : ℝ)*H*(N : ℝ)^2/Y := by
    have h1 := mul_le_mul_of_nonneg_left (hcard.trans hNdiv) (show 0≤(J : ℝ)*H by positivity)
    have h2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hoff (show 0≤(J : ℝ)*H by positivity)) hYp.le
    calc
      _ ≤ (J : ℝ)*H*((N : ℝ)^2/Y)+(J : ℝ)*H*(N : ℝ)^2/Y := add_le_add h1 h2
      _ = _ := by ring
  have hpow : T^δ*T^δ=T^ε := by
    rw [← Real.rpow_add hTp]
    congr 1
    dsimp [δ]
    ring
  have hpre : basicMoment A d H J α σ≤
      2*(J : ℝ)*H*(N : ℝ)^2/Y+
        (2*(J : ℝ)*H*Lh)*(Cd*T^δ)*(Ch*(N : ℝ)^2*T^δ*L^2*E) := by
    apply hreduction.trans
    apply add_le_add hdiag
    have hhh := hweighted.trans (mul_le_mul_of_nonneg_left hheightBound (show 0≤Cd*T^δ by positivity))
    convert mul_le_mul_of_nonneg_left hhh (show 0≤2*(J : ℝ)*H*Lh by positivity) using 1 <;>
      dsimp [V,T,L,Lh,E] <;> ring
  have hbase : (J : ℝ)*H*(N : ℝ)^2/Y≤B := by
    have hpow1 : 1≤T^ε := Real.one_le_rpow hT hε.le
    have hfactor : 1≤T^ε*L^2*Lh := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hpow1 (one_le_pow₀ hL)) hLh
    have hEinv : 1/Y≤E := by
      dsimp [E]
      exact le_add_of_nonneg_right (one_div_pos.mpr (Real.rpow_pos_of_pos (height_pos _ _) _)).le
    calc
      _ = ((J : ℝ)*H*(N : ℝ)^2)*(1/Y) := by ring
      _ ≤ ((J : ℝ)*H*(N : ℝ)^2)*((T^ε*L^2*Lh)*E) :=
        mul_le_mul_of_nonneg_left (hEinv.trans (le_mul_of_one_le_left hEp.le hfactor)) (by positivity)
      _ = _ := by dsimp [B]; ring
  have hid : (2*(J : ℝ)*H*Lh)*(Cd*T^δ)*(Ch*(N : ℝ)^2*T^δ*L^2*E)=2*Cd*Ch*B := by
    calc
      _ = (2*Cd*Ch*(J : ℝ)*H*(N : ℝ)^2*L^2*Lh*E)*(T^δ*T^δ) := by ring
      _ = _ := by rw [hpow]; dsimp [B]; ring
  rw [hid] at hpre
  calc
    _ ≤ 2*(J : ℝ)*H*(N : ℝ)^2/Y+2*Cd*Ch*B := hpre
    _ ≤ 2*B+2*Cd*Ch*B := by
      apply add_le_add_right
      convert mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ)≤2) using 1 <;> ring
    _ = _ := by dsimp [B,V,T,L,Lh,E]; ring

#print axioms basic_moment_height_bound
end Waring.PolicyCompletionBasicEstimate
