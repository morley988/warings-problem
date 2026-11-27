import Waring.PolicyCompletionShallowHeight
import Waring.PolicyCompletionShallowLoss

/-!
# The actual shallow second coefficient moment

This closes the shallow estimate corresponding to Vaughan--Wooley (1995),
Lemma4.2. A common Dirichlet approximant is constructed, both actual
frequency branches are estimated, and every divisor and logarithmic loss
is absorbed uniformly on polynomial-size ranges. The intrinsic-height
form needs no separate rational-matching hypothesis.
-/

noncomputable section
open scoped BigOperators Classical
namespace Waring.PolicyCompletionShallowEstimate
open RationalHeight BasicMatching PolicyCompletionBasicMoment
open PolicyCompletionShallowArithmetic PolicyCompletionShallowActual
open PolicyCompletionShallowKernel PolicyCompletionShallowHeight
open PolicyCompletionShallowLoss

set_option maxHeartbeats 1000000 in
theorem shallow_moment_uniform {k : ℕ} (hk : 3≤k) {B ε : ℝ} (hB : 0≤B) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀P : ℝ,2≤P→∀(A : Finset ℕ) (H N J : ℕ),0<H→0<N→
      (A⊆Finset.Icc 1 N)→∀M : ℝ,0≤M→M≤N→(∀m∈A,M<(m : ℝ))→
      (N : ℝ)≤P^B→(H : ℝ)≤P^B→((H^3*N^(2*k) : ℕ) : ℝ)≤P^B→
      ∀(α : ℝ) (σ : ℕ→ℝ),
      basicMoment A (2*k) H J α σ≤C*P^ε*
        ((J : ℝ)*H*(N : ℝ)^2/(height ((H : ℝ)^3*J*M^(2*k)) α)^(1/(k : ℝ))+
          (J : ℝ)*H*N+(H : ℝ)^3*(N : ℝ)^(2*k)) := by
  let E := 2*B+2
  have hE : 0≤E := by dsimp [E]; positivity
  obtain ⟨δ,D,hδ,hD,hloss⟩ := shallow_loss_bounds hE hε
  obtain ⟨Cd,hCd,hdivisible⟩ := divisible_positive_height_bound hk hδ
  obtain ⟨Cn,hCn,hnondivisible⟩ := nondivisor_frequency_sum (by omega : 0<k) hδ
  let K := 1+Cd*D+Cn*D
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨3*K,by positivity,?_⟩
  intro P hP A H N J hH hN hA M hM hMN hlow hNup hHup hTup α σ
  let T : ℕ := H^3*N^(2*k)
  have hT : 0<T := Nat.mul_pos (pow_pos hH _) (pow_pos hN _)
  have hT1 : (1 : ℝ)≤T := by exact_mod_cast hT
  have hTpos : (0 : ℝ)<T := by exact_mod_cast hT
  have hP1 : 1≤P := by linarith
  have hPp : 0<P := by linarith
  have hBE : B≤E := by dsimp [E]; linarith
  have hPE : P^B≤P^E := Real.rpow_le_rpow_of_exponent_le hP1 hBE
  obtain ⟨r,hq,herr⟩ := exists_approximant (show 1≤2*(T : ℝ) by linarith) α
  have herr' : 2*(T : ℝ)*error α r≤1 := by
    have hh := (le_div_iff₀ (show 0<2*(T : ℝ) by positivity)).mp herr
    nlinarith only [hh]
  have hqE : (r.den : ℝ)≤P^E := by
    calc
      _ ≤ 2*(T : ℝ) := hq
      _ ≤ P*P^B := mul_le_mul hP hTup (by positivity) hPp.le
      _ = P^(B+1) := by rw [Real.rpow_add hPp,Real.rpow_one]; ring
      _ ≤ P^E := Real.rpow_le_rpow_of_exponent_le hP1 (by dsimp [E]; linarith)
  have hscaleE : 2*(N : ℝ)*r.den≤P^E := by
    calc
      _ ≤ 4*(N : ℝ)*(T : ℝ) := by
        have hh := mul_le_mul_of_nonneg_left hq (show 0≤2*(N : ℝ) by positivity)
        nlinarith only [hh]
      _ ≤ 4*P^B*P^B := by gcongr
      _ ≤ P^2*P^B*P^B := by gcongr; nlinarith only [hP,sq_nonneg (P-2)]
      _ = P^E := by
        rw [← Real.rpow_natCast P 2,← Real.rpow_add hPp,← Real.rpow_add hPp]
        congr 1
        dsimp [E]
        norm_num
        ring
  obtain ⟨hmainLoss,hboundaryLoss,herrorLoss⟩ := hloss P hP1 N H T r.den hN hH hT r.pos
    (hHup.trans hPE) (hTup.trans hPE) hqE hscaleE
  let X := (J : ℝ)*H*(N : ℝ)^2/(height ((H : ℝ)^3*J*M^(2*k)) α)^(1/(k : ℝ))
  let Y := (J : ℝ)*H*N
  have hX : 0≤X := by dsimp [X]; exact div_nonneg (by positivity) (Real.rpow_nonneg (height_pos _ _).le _)
  have hY : 0≤Y := by dsimp [Y]; positivity
  have hdiv := hdivisible A H N J hH hN hA M hM hMN hlow r α herr'
  have hdivFinal : divisiblePositiveKernel A k H J r α≤Cd*D*P^ε*(X+Y) := by
    apply hdiv.trans
    calc
      _ = Cd*((2*(N : ℝ)*r.den)^δ*(r.den.divisors.card : ℝ)^3*
            (1+Real.log (2*(N : ℝ)))*(1+Real.log H)*X+
          (2*(N : ℝ)*r.den)^δ*(1+Real.log N)*Y) := by dsimp [X,Y]; ring
      _ ≤ Cd*(D*P^ε*X+D*P^ε*Y) := mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hmainLoss hX)
          (mul_le_mul_of_nonneg_right hboundaryLoss hY)) hCd.le
      _ = _ := by ring
  have hS : ∀v∈positiveFamily A H,v.2.1<v.2.2 := fun v hv=>(positiveFamily_bounds (by omega : 0<k) hA hv).1
  have hmap : ∀v∈positiveFamily A H,differenceFrequency k v∈Finset.Icc 1 T :=
    fun v hv=>(positiveFamily_bounds (by omega : 0<k) hA hv).2
  have hclog : (r.den : ℝ)≤(2 : ℝ)^(Nat.clog 2 r.den) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1<2) r.den
  have hnon := hnondivisible T hT (positiveFamily A H) hS hmap r α hq herr' J (Nat.clog 2 r.den) hclog
  have hnonFinal :
      (∑v∈(positiveFamily A H).filter (fun v=>¬r.den∣differenceFrequency k v),
        linearSumBound J (α*(differenceFrequency k v : ℝ)))≤Cn*D*P^ε*(T : ℝ) := by
    apply hnon.trans
    calc
      _ = Cn*(T : ℝ)*((T : ℝ)^δ*(Nat.clog 2 r.den+1 : ℕ)) := by
        rw [Real.rpow_add hTpos,Real.rpow_one]
        ring
      _ ≤ Cn*(T : ℝ)*(D*P^ε) := mul_le_mul_of_nonneg_left herrorLoss (by positivity)
      _ = _ := by ring
  have hcard : (A.card : ℝ)≤N := by
    have hh := Finset.card_le_card hA
    simpa using (show (A.card : ℝ)≤((Finset.Icc 1 N).card : ℝ) by exact_mod_cast hh)
  have hdiag : (J : ℝ)*H*A.card≤Y := mul_le_mul_of_nonneg_left hcard (by positivity)
  have hCdD : 0≤Cd*D := by positivity
  have hCnD : 0≤Cn*D := by positivity
  have hK1 : 1≤K := by dsimp [K]; linarith only [hCdD,hCnD]
  have hKd : Cd*D≤K := by dsimp [K]; linarith only [hCnD]
  have hKn : Cn*D≤K := by dsimp [K]; linarith only [hCdD]
  have hPe : 1≤P^ε := Real.one_le_rpow hP1 hε.le
  have hKP : 1≤K*P^ε := one_le_mul_of_one_le_of_one_le hK1 hPe
  have hdiagK : (J : ℝ)*H*A.card≤K*P^ε*Y :=
    hdiag.trans (le_mul_of_one_le_left hY hKP)
  have hdivK : divisiblePositiveKernel A k H J r α≤K*P^ε*(X+Y) :=
    hdivFinal.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKd (Real.rpow_nonneg hPp.le _)) (add_nonneg hX hY))
  have hnonK := hnonFinal.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hKn (Real.rpow_nonneg hPp.le _)) (show (0 : ℝ)≤T by positivity))
  have hb := basicMoment_le_positiveKernel A k H J α σ
  rw [positiveKernel_partition A k H J r α] at hb
  calc
    _ ≤ (J : ℝ)*H*A.card+2*(divisiblePositiveKernel A k H J r α+
        ∑v∈(positiveFamily A H).filter (fun v=>¬r.den∣differenceFrequency k v),
          linearSumBound J (α*(differenceFrequency k v : ℝ))) := hb
    _ ≤ K*P^ε*Y+2*(K*P^ε*(X+Y)+K*P^ε*(T : ℝ)) :=
      add_le_add hdiagK (mul_le_mul_of_nonneg_left (add_le_add hdivK hnonK) (by norm_num))
    _ = K*P^ε*(Y+2*(X+Y+(T : ℝ))) := by ring
    _ ≤ K*P^ε*(3*(X+Y+(T : ℝ))) := mul_le_mul_of_nonneg_left
      (by
        have hT0 : (0 : ℝ)≤T := by positivity
        linarith only [hX,hY,hT0]) (by positivity)
    _ = _ := by dsimp [X,Y,T]; push_cast; ring

#print axioms shallow_moment_uniform
end Waring.PolicyCompletionShallowEstimate
