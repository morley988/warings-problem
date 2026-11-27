import WaringFieldSmall.Physical

/-! # Continuous conductors for a finite list of elementary Weyl steps -/
noncomputable section
open WaringEnvelope WaringLinear
namespace WaringFieldSmall

def specConfig (K : ℕ) : WaringEnvelope.Config := ⟨K,K,1,0,0,0,0⟩
def liftHeight (g : ℕ) := g*(10^23/2)
def testRow (K data code : ℕ) : Bool :=
  let s := unpack data
  0<K && 0<s.gain && modulusScale<s.modulus && s.modulus<modulusScale*K &&
    chain (specConfig K) s.modulus (ceilDiv (20001*liftHeight s.gain) 10000) 16 B code
def testList (K : ℕ) : List ℕ → List ℕ → Bool
  | [],[] => true
  | u::us,c::cs => testRow K u c && testList K us cs
  | _,_ => false

theorem testList_coverage {K k : ℕ} {data codes : List ℕ} (hk : K≤k) (hmax : k<180000^2)
    (h : testList K data codes=true) (u : ℕ) (hu : u∈data) :
    let s := unpack u
    let M := (s.modulus:ℝ)/modulusScale
    let z := (s.gain:ℝ)/(2*scale)
    0<z ∧ 1<M ∧ M<k ∧ ∃ σ, 2*z<σ ∧ ∀ v : ℝ, 1<v → v≤M → fieldConductorStage k (M/k) v σ := by
  have hex : ∃ code, testRow K u code=true := by
    induction data generalizing codes with
    | nil => simp at hu
    | cons s ss ih =>
      cases codes with
      | nil => simp [testList] at h
      | cons c cs =>
        have ⟨hw,hs⟩ : testRow K s c=true ∧ testList K ss cs=true := by
          simpa only [testList,Bool.and_eq_true] using h
        rcases List.mem_cons.mp hu with e|mem
        · subst u;exact ⟨c,hw⟩
        · exact ih hs mem
  obtain ⟨code,hc⟩ := hex
  simp only [testRow,Bool.and_eq_true,decide_eq_true_eq,and_assoc] at hc
  obtain ⟨hK,hg,hm,hcap,chainOK⟩ := hc
  let s := unpack u
  have hB : (0:ℝ)<modulusScale := by norm_num [modulusScale]
  have hg' : (0:ℝ)<s.gain := by exact_mod_cast hg
  have hm' : (modulusScale:ℝ)<s.modulus := by exact_mod_cast hm
  have hcap' : (s.modulus:ℝ)<modulusScale*k := by exact_mod_cast hcap.trans_le (Nat.mul_le_mul_left _ hk)
  have hzh : (s.gain:ℝ)/(2*scale)=(liftHeight s.gain:ℝ)/T := by
    norm_num [scale,liftHeight,T];ring
  dsimp only
  let sig := ceilDiv (20001*liftHeight s.gain) 10000
  refine ⟨div_pos hg' (by norm_num [scale]),(one_lt_div hB).2 hm',(div_lt_iff₀ hB).2 ?_,(sig:ℝ)/T,?_,?_⟩
  · linarith only [hcap']
  · rw [hzh]
    exact strict_height_saving (liftHeight s.gain) (Nat.mul_pos hg (by decide))
  · intro v hv hvm
    have hstage := chain_sound_of_positive (specConfig K) s.modulus _ code v hK (by change 0<1;decide) chainOK hv hvm
    have hth := actualTheta_le_stage (specConfig K) s.modulus k hK (by change 0<1;decide) hk (Or.inl hK.ne')
    simp only [fieldConductorStage,if_pos hmax]
    apply Or.inl
    apply hstage.mono hk _ le_rfl
    convert hth using 1
    unfold actualTheta
    change ((s.modulus:ℝ)/modulusScale)/k=s.modulus/(modulusScale*k)
    ring

#print axioms testList_coverage
end WaringFieldSmall
