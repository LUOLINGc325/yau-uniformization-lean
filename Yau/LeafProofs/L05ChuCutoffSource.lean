import Yau.LeafProofs.L05ChuCutoffJets

noncomputable section

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

def chuFrozenLowSource {n : ℕ} (a : Mat n) (phi : Space n → ℝ) (theta : ℝ → ℝ)
    (u : Point n → ℝ) (p : Point n) : ℝ :=
  -(theta p.2)*L16Aux.spatialCutoffCommutator (fun _ => a) (fun _ _ => 0) phi u p+
    deriv theta p.2*(phi p.1*u p)

theorem chuFrozenCutoffSource_split {n : ℕ} {T : Sym n → Point n → Sym n} {K beta : ℝ}
    (hT : ChuH2 T K beta) (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n)
    (hp0 : p0 ∈ backward 1) (phi : Space n → ℝ) (theta : ℝ → ℝ) (u : Point n → ℝ) (p : Point n) :
    chuFrozenCutoffSource hT F A0 p0 hp0 phi theta u p=
      (theta p.2*phi p.1)*chuFrozenResidual hT F A0 p0 hp0 u p+
        chuFrozenLowSource (chuFrozenSlope hT F A0 p0 hp0 : Mat n) phi theta u p := by
  unfold chuFrozenCutoffSource chuFrozenLowSource
  ring

theorem chu_holderBound_constant {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {gamma C : ℝ} {Q : Set (Point n)} (v : V) (hC : 0 ≤ C) (hv : ‖v‖ ≤ C) :
    HolderBound gamma Q (fun _ => v) C := by
  refine ⟨hC,fun _ _ => hv,?_⟩
  intro p hp q hq
  rw [sub_self,norm_zero]
  exact mul_nonneg hC (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _))

def chuFrozenLowSourceBudget (n : ℕ) (M E0 E1 E2 C D D1 : ℝ) : ℝ :=
  2*D*(L16Aux.spatialCutoffCommutatorBudget n M E1 E2*C)+4*D1*E0*C

set_option maxHeartbeats 1600000 in
theorem chuFrozenLowSource_holderBound {n : ℕ} {O : Set (Space n)} {l r gamma M E0 E1 E2 C D D1 : ℝ}
    {a : Mat n} (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) {phi : Space n → ℝ} (hSupport : tsupport phi ⊆ O)
    {u : Point n → ℝ} {theta : ℝ → ℝ}
    (h0 : HolderBound gamma (cylinder Set.univ l r) (fun p => phi p.1) E0)
    (hD : HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ phi p.1) E1)
    (hDD : HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ phi) p.1) E2)
    (hLow : HolderBound gamma (cylinder O l r) (fun p => (u p,spatialD u p)) C)
    (htheta : HolderBound gamma (cylinder Set.univ l r) (fun p : Point n => theta p.2) D)
    (hthetaD : HolderBound gamma (cylinder Set.univ l r) (fun p : Point n => deriv theta p.2) D1) :
    HolderBound gamma (cylinder Set.univ l r) (chuFrozenLowSource a phi theta u)
      (chuFrozenLowSourceBudget n M E0 E1 E2 C D D1) := by
  let P : Set (Point n) := cylinder Set.univ l r
  let U : Set (Point n) := O ×ˢ Set.univ
  have hA : HolderBound gamma P (fun _ => a) M := chu_holderBound_constant a hM ha
  have hb (i : RIdx n) : HolderBound gamma P (fun _ => (0:ℝ)) M :=
    chu_holderBound_constant 0 hM (by simpa only [norm_zero] using hM)
  have hcomm := L16Aux.spatialCutoffCommutator_holderBound_local hA hb hD hDD hSupport hLow
  have hFirst := L16Aux.holderBound_mul (L16Aux.holderBound_neg htheta) hcomm
  have hUP : U ∩ P=cylinder O l r := by ext p; simp [U,P,cylinder]
  have hu0 : HolderBound gamma (U ∩ P) u C := by
    simpa only [hUP] using L16Aux.holderBound_fst hLow
  have hphiZero (p : Point n) (hp : p ∈ P) (hpU : p ∉ U) : phi p.1=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hpU ⟨hSupport h,Set.mem_univ _⟩
  have hPhiU := L16Aux.holderBound_smul_cutoff_extension h0 hu0 hphiZero
  have hPhiU' : HolderBound gamma P (fun p => phi p.1*u p) (2*E0*C) := by
    simpa only [smul_eq_mul] using hPhiU
  have hSecond := L16Aux.holderBound_mul hthetaD hPhiU'
  have hh := L16Aux.holderBound_add hFirst hSecond
  convert! hh using 1
  unfold chuFrozenLowSourceBudget
  ring

end Yau.LeafProofs.L05Aux
