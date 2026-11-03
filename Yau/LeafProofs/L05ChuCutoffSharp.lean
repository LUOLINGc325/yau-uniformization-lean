import Yau.LeafProofs.L05ChuSlabSharp
import Yau.LeafProofs.L05ChuCutoffCoarse

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuCutoffSharpDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuCutoffSharpDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuCutoffSharpHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05ChuCutoffSharpHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

def chuCutoffCoarseSourceBudget (n : ℕ) (Ma E0 E1 E2 Clow D D1 MR : ℝ) : ℝ :=
  4*D*E0*MR+(2*D*L16Aux.spatialCutoffCommutatorBudget n Ma E1 E2+4*D1*E0)*Clow

set_option maxHeartbeats 2400000 in
theorem chu_frozen_cutoff_slab_sharp (n : ℕ) (hn : 0 < n) (ell upper : ℝ)
    (hell : 0 < ell) (hUpper : ell ≤ upper) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : Sym n → Point n → Sym n) (K beta : ℝ) (hT : ChuH2 T K beta)
        (F : Sym n → Point n → ℝ) (A0 : Sym n) (p0 : Point n) (hp0 : p0 ∈ backward 1)
        (O : Set (Space n)) (l r eta gamma Ma MR MH epsilon A : ℝ)
        (e0 e1 e2 ce d d1 E0 E1 E2 cg D D1 : ℝ) (phi : Space n → ℝ) (u : Point n → ℝ),
      l < r → r-l ≤ 1 → 0 < eta → eta < 1 → 0 < gamma → gamma < 1 →
      IsOpen O → ContDiff ℝ 2 phi → tsupport phi ⊆ O → cylinder O l r ⊆ backward 1 →
      C2 (backward 1) u → 0 ≤ Ma → 0 ≤ epsilon → 0 ≤ A →
      ‖(chuFrozenSlope hT F A0 p0 hp0 : Mat n)‖ ≤ Ma →
      Elliptic (cylinder Set.univ l r) (fun _ => (chuFrozenSlope hT F A0 p0 hp0 : Mat n)) ell upper →
      (∀ x, |phi x| ≤ 1) →
      HolderBound eta (cylinder Set.univ l r) (fun p => phi p.1) e0 →
      HolderBound eta (cylinder Set.univ l r) (fun p => fderiv ℝ phi p.1) e1 →
      HolderBound eta (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ phi) p.1) e2 →
      HolderBound gamma (cylinder Set.univ l r) (fun p => phi p.1) E0 →
      HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ phi p.1) E1 →
      HolderBound gamma (cylinder Set.univ l r) (fun p => fderiv ℝ (fderiv ℝ phi) p.1) E2 →
      HolderBound eta (cylinder O l r) (fun p => (u p,spatialD u p)) ce →
      HolderBound gamma (cylinder O l r) (fun p => (u p,spatialD u p)) cg →
      HolderBound eta (cylinder O l r) (spatialDD u) MH →
      HolderBound eta (cylinder O l r) (chuFrozenResidual hT F A0 p0 hp0 u) MR →
      HolderBound eta (cylinder Set.univ l r) (fun p : Point n => chuCausalTimeCutoff l r p.2) d →
      HolderBound eta (cylinder Set.univ l r) (fun p : Point n => deriv (chuCausalTimeCutoff l r) p.2) d1 →
      HolderBound gamma (cylinder Set.univ l r) (fun p : Point n => chuCausalTimeCutoff l r p.2) D →
      HolderBound gamma (cylinder Set.univ l r) (fun p : Point n => deriv (chuCausalTimeCutoff l r) p.2) D1 →
      (∀ p ∈ cylinder O l r, ∀ q ∈ cylinder O l r,
        |chuFrozenResidual hT F A0 p0 hp0 u p-chuFrozenResidual hT F A0 p0 hp0 u q| ≤
          epsilon*‖spatialDD u p-spatialDD u q‖+A*holderWeight gamma p q) →
      (C*epsilon)*diniPowerConstant gamma ≤ 1/2 → (C*epsilon)*diniPowerConstant eta ≤ 1/2 →
      powerBound gamma
        (2*(C*((2*chuFrozenCutoffAbsorptionBudget n A E0 E1 E2 cg D D1 Ma MR MH epsilon)*diniPowerConstant gamma+
          chuCutoffCoarseSourceBudget n Ma e0 e1 e2 ce d d1 MR)))
        (chuOscillation (cylinder Set.univ l r)
          (spatialDD (fun p => chuCausalTimeCutoff l r p.2*(phi p.1*u p)))) := by
  obtain ⟨C,hC,hSharp⟩ := constant_causal_slab_sharp_oscillation n hn ell upper hell hUpper
  refine ⟨C,hC,?_⟩
  intro T K beta hT F A0 p0 hp0 O l r eta gamma Ma MR MH epsilon A e0 e1 e2 ce d d1 E0 E1 E2 cg D D1 phi u
    hlr hDuration he he1 hg hg1 hO hphi hSupport hQ hu hMa heps hA ha hEll hUnitPhi
    he0 heD heDD h0 hD hDD hLowEta hLowGamma hH hR hThetaEta hThetaDEta hThetaGamma hThetaDGamma
    hResidual hSmallGamma hSmallEta
  let theta : ℝ → ℝ := chuCausalTimeCutoff l r
  let w : Point n → ℝ := fun p => theta p.2*(phi p.1*u p)
  let g : Point n → ℝ := chuFrozenCutoffSource hT F A0 p0 hp0 phi theta u
  let FG : ℝ := chuCutoffCoarseSourceBudget n Ma e0 e1 e2 ce d d1 MR
  let AG : ℝ := chuFrozenCutoffAbsorptionBudget n A E0 E1 E2 cg D D1 Ma MR MH epsilon
  have huLocal := chu_c2_cylinder_restrict_backward hlr hQ hu
  have hClassical := chu_frozen_cutoff_classical hT F A0 p0 hp0 hu hO hlr hQ hphi hSupport
    ((chuCausalTimeCutoff_contDiff l r).of_le (by norm_num : (1:WithTop ℕ∞) ≤ ∞))
  have hHG := chu_cutoff_hessian_coarse_holder hO hphi hSupport huLocal he0 heD heDD hLowEta hH hThetaEta
  have hGF : HolderBound eta (cylinder Set.univ l r) g FG :=
    chu_cutoff_source_coarse_holder hT F A0 p0 hp0 hSupport hMa ha he0 heD heDD hLowEta hR hThetaEta hThetaDEta
  have hRvalue (p : Point n) (hp : p ∈ cylinder O l r) : |chuFrozenResidual hT F A0 p0 hp0 u p| ≤ MR := by
    simpa only [Real.norm_eq_abs] using hR.2.1 p hp
  have hPair (p : Point n) (hp : p ∈ cylinder Set.univ l r) (q : Point n) (hq : q ∈ cylinder Set.univ l r) :
      |g p-g q| ≤ epsilon*‖spatialDD w p-spatialDD w q‖+AG*holderWeight gamma p q :=
    chu_frozen_cutoff_source_pair hT F A0 p0 hp0 hO hphi hSupport huLocal heps hA hR.1 hH.1 hMa ha
      h0 hD hDD hLowGamma hThetaGamma hThetaDGamma hUnitPhi
      (fun a => by rw [abs_of_nonneg (chuCausalTimeCutoff_mem_Icc l r a).1]; exact (chuCausalTimeCutoff_mem_Icc l r a).2)
      hRvalue hH.2.1 hResidual hp hq
  have hE0 := h0.1
  have hE1 := hD.1
  have hE2 := hDD.1
  have hCG := hLowGamma.1
  have hDG := hThetaGamma.1
  have hD1G := hThetaDGamma.1
  have hMR := hR.1
  have hMH := hH.1
  have hAG : 0 ≤ AG := by
    dsimp only [AG,chuFrozenCutoffAbsorptionBudget,chuFrozenLowSourceBudget,L16Aux.spatialCutoffCommutatorBudget]
    positivity
  have hwBound (p : Point n) (hp : p ∈ cylinder Set.univ l r) : |w p| ≤ ce := by
    by_cases hpO : p.1 ∈ O
    · have huBound : |u p| ≤ ce := by
        simpa only [Real.norm_eq_abs] using (L16Aux.holderBound_fst hLowEta).2.1 p ⟨hpO,hp.2⟩
      have hTheta : |theta p.2| ≤ 1 := by
        rw [abs_of_nonneg (chuCausalTimeCutoff_mem_Icc l r p.2).1]
        exact (chuCausalTimeCutoff_mem_Icc l r p.2).2
      have hCut : |theta p.2*phi p.1| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul hTheta (hUnitPhi p.1) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul 1)
      have heq : w p=(theta p.2*phi p.1)*u p := by dsimp only [w]; ring
      rw [heq,abs_mul]
      exact (mul_le_mul hCut huBound (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul ce)
    · have hPhiZero : phi p.1=0 := image_eq_zero_of_notMem_tsupport (fun h => hpO (hSupport h))
      simpa only [w,hPhiZero,zero_mul,mul_zero,abs_zero] using hLowEta.1
  have hZero (x : Space n) : w (x,l)=0 ∧ g (x,l)=0 :=
    chu_frozen_cutoff_zero_past hT F A0 p0 hp0 phi u hlr (p := (x,l)) le_rfl
  exact hSharp (chuFrozenSlope hT F A0 p0 hp0 : Mat n) l r eta gamma FG FG ce
    (4*d*e0*MH+2*d*((4*e1+2*e2)*ce)) epsilon AG g w hlr hDuration he he1 hg hg1
    hGF.1 hGF.1 hLowEta.1 heps hAG hEll hGF
    (fun p hp => by simpa only [Real.norm_eq_abs] using hGF.2.1 p hp) (fun x => (hZero x).2)
    hClassical.1 hwBound (fun x => (hZero x).1)
    (fun p hp => hClassical.2 p ⟨Set.mem_univ _,hp.2.1.le,hp.2.2⟩)
    hHG hPair hSmallGamma hSmallEta

end Yau.LeafProofs.L05Aux
