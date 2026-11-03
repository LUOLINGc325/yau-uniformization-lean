import Yau.LeafProofs.L05ChuCutoffSharp
import Yau.LeafProofs.L05ChuAbsorptionChoice
import Yau.LeafProofs.L05ChuPatchResidual
import Yau.LeafProofs.L05ChuPatchPlateau
import Yau.LeafProofs.L05ChuTimeCutoffBudget
import Yau.LeafProofs.L05ChuLowJetBudget
import Yau.LeafProofs.L05ChuFrozenElliptic

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

local instance l05ChuSharpHessianDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuSharpHessianDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuSharpHessianHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05ChuSharpHessianHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

set_option maxHeartbeats 4000000 in
theorem chu_sharp_hessian_of_coarse (n : ℕ) (hn : 0 < n) (ell L K alpha beta eta gamma fB M : ℝ)
    (hell : 0 < ell) (hL : ell ≤ L) (hK : 0 < K) (hM : 0 ≤ M)
    (he : 0 < eta) (he1 : eta < 1) (hb : 0 < beta) (hg : 0 < gamma) (hg1 : gamma < 1)
    (hga : gamma ≤ alpha) (hgb : gamma ≤ beta) (hfB : 0 ≤ fB) (omega : ℝ → ℝ) (hm : Modulus omega) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E U : Set (Sym n)) (F : Sym n → Point n → ℝ) (T : Sym n → Point n → Sym n)
        (S : Point n → Sym n) (f u : Point n → ℝ),
      Convex ℝ E → ChuH1 E U F ell L K beta → ChuH2 T K beta → ChuH3 S K beta →
      ChuDerivativeModulus E F omega → HolderBound alpha (backward 1) f fB → C2 (backward 1) u →
      SchauderBound eta (backward (3/4)) u M →
      (∀ p ∈ backward 1, S p+T (hessian u p) p ∈ E) →
      (∀ p ∈ backward 1, timeD (backward 1) u p-F (S p+T (hessian u p) p) p=f p) →
      HolderBound gamma (backward (1/2)) (spatialDD u) C := by
  have hCL := bellmanMatrixConstant_nonneg n (hell.le.trans hL)
  have hCT := chuTransformNormConstant_nonneg n hK.le
  have hDim := chuHessianTransportConstant_pos n
  obtain ⟨Ck,hCk,hCutoff⟩ := chu_frozen_cutoff_slab_sharp n hn (chuCoarseLower ell K)
    (chuCoarseUpper n ell L K) (chuCoarseLower_pos hell hK) (chuCoarseLower_le_upper n ell L K)
  obtain ⟨epsilon,heps,heps1,hSmallEta,hSmallGamma⟩ := chu_numeric_absorption_choice hCk he he1 hg hg1
  obtain ⟨rho,hrho,hrho1,hResidual⟩ := chu_residual_on_causal_patch (fB := fB) hm hell.le hL hK.le hM he hb hg.le hga hgb heps
  let h : ℝ := min (rho/4) (1/32)
  have hh : 0 < h := lt_min (by positivity) (by norm_num)
  have hhSmall : h ≤ (1/32:ℝ) := min_le_right _ _
  have hh1 : h ≤ 1 := hhSmall.trans (by norm_num)
  have hhRho : 4*h ≤ rho := by have hs := min_le_left (rho/4) (1/32:ℝ); change h ≤ rho/4 at hs; linarith only [hs]
  have hDuration : 4*h^2 ≤ 1 := by
    have hs : h^2 ≤ (1/32:ℝ)^2 := (sq_le_sq₀ hh.le (by norm_num)).mpr hhSmall
    nlinarith only [hs]
  obtain ⟨Ce,hCe,hSpatialEta⟩ := chu_spatial_cutoff_budgets (n := n) he he1
  obtain ⟨Cg,hCg,hSpatialGamma⟩ := chu_spatial_cutoff_budgets (n := n) hg hg1
  obtain ⟨Te,hTe,hTimeEta⟩ := chuCausalTimeCutoff_uniform_holder_jets (n := n) he he1
  obtain ⟨Tg,hTg,hTimeGamma⟩ := chuCausalTimeCutoff_uniform_holder_jets (n := n) hg hg1
  let e0 : ℝ := 2*(h⁻¹*Ce)*h^(1-eta)
  let e1 : ℝ := 2*((h⁻¹)^2*Ce)*h^(1-eta)
  let e2 : ℝ := 2*((h⁻¹)^3*Ce)*h^(1-eta)
  let E0 : ℝ := 2*(h⁻¹*Cg)*h^(1-gamma)
  let E1 : ℝ := 2*((h⁻¹)^2*Cg)*h^(1-gamma)
  let E2 : ℝ := 2*((h⁻¹)^3*Cg)*h^(1-gamma)
  let de : ℝ := Te/(4*h^2)^2
  let dg : ℝ := Tg/(4*h^2)^2
  let ce : ℝ := chuLowJetBudget eta M
  let cg : ℝ := chuLowJetBudget gamma M
  let MR : ℝ := chuFrozenResidualBudget n L K M
  let Ma : ℝ := (2*n:ℝ)*chuCoarseUpper n ell L K
  let A : ℝ := chuResidualSourceConstant n L K fB (chuHessianTransportConstant n*M)
    (chuAnchorModulusBound n K (chuHessianTransportConstant n*M) omega)
  let FG : ℝ := chuCutoffCoarseSourceBudget n Ma e0 e1 e2 ce de de MR
  let AG : ℝ := chuFrozenCutoffAbsorptionBudget n A E0 E1 E2 cg dg dg Ma MR M epsilon
  let Csharp : ℝ := 2*(Ck*((2*AG)*diniPowerConstant gamma+FG))
  have hUpper0 : 0 ≤ chuCoarseUpper n ell L K := (chuCoarseLower_pos hell hK).le.trans (chuCoarseLower_le_upper n ell L K)
  have hMa : 0 ≤ Ma := by dsimp only [Ma]; positivity
  have hMR : 0 ≤ MR := by dsimp only [MR,chuFrozenResidualBudget]; positivity
  have hArg : 0 ≤ 2*chuTransformNormConstant n K*(chuHessianTransportConstant n*M)+
      2*K*(1+2*(chuHessianTransportConstant n*M))+1 := by positivity
  have hOmega := hm.2.1 _ hArg
  have hA : 0 ≤ A := by dsimp only [A,chuResidualSourceConstant,chuAnchorModulusBound]; positivity
  have he0 : 0 ≤ e0 := by dsimp only [e0]; positivity
  have he1v : 0 ≤ e1 := by dsimp only [e1]; positivity
  have he2 : 0 ≤ e2 := by dsimp only [e2]; positivity
  have hE0 : 0 ≤ E0 := by dsimp only [E0]; positivity
  have hE1 : 0 ≤ E1 := by dsimp only [E1]; positivity
  have hE2 : 0 ≤ E2 := by dsimp only [E2]; positivity
  have hde : 0 ≤ de := by dsimp only [de]; positivity
  have hdg : 0 ≤ dg := by dsimp only [dg]; positivity
  have hce : 0 ≤ ce := by dsimp only [ce,chuLowJetBudget]; positivity
  have hcg : 0 ≤ cg := by dsimp only [cg,chuLowJetBudget]; positivity
  have hFG : 0 ≤ FG := by dsimp only [FG,chuCutoffCoarseSourceBudget,L16Aux.spatialCutoffCommutatorBudget]; positivity
  have hAG : 0 ≤ AG := by dsimp only [AG,chuFrozenCutoffAbsorptionBudget,chuFrozenLowSourceBudget,L16Aux.spatialCutoffCommutatorBudget]; positivity
  have hkGamma : 0 ≤ diniPowerConstant gamma := by unfold diniPowerConstant; positivity
  have hCsharp : 0 ≤ Csharp := by dsimp only [Csharp]; positivity
  let MW : ℝ := 4*de*e0*M+2*de*((4*e1+2*e2)*ce)
  let Cfinal : ℝ := 1+M+Csharp+2*M*(h/2)^(-gamma)
  have hCfinal : 0 < Cfinal := by dsimp only [Cfinal]; positivity
  refine ⟨Cfinal,hCfinal,?_⟩
  intro E U F T S f u hE hF hT hS hDF hf hu hCoarse hRange hPDE
  have hBig : backward (n := n) (3/4) ⊆ backward 1 := chu_backward_subset (by norm_num) (by norm_num)
  have hHalf : backward (n := n) (1/2) ⊆ backward (3/4) := chu_backward_subset (by norm_num) (by norm_num)
  have hHalfBig : backward (n := n) (1/2) ⊆ backward 1 := hHalf.trans hBig
  have hLowEta := chu_coarse_lowJet_holder he he1 hCoarse
  have hLowGamma := chu_coarse_lowJet_holder hg hg1 hCoarse
  have hHcoarse := hCoarse.2.2.2.1
  let w : Point n → Point n → ℝ := fun p0 p => chuCausalTimeCutoff (p0.2-4*h^2) p0.2 p.2*
    (L16Aux.innerPatchBump h hh p0.1 p.1*u p)
  have hPatchData (p0 : Point n) (hp0 : p0 ∈ backward (1/2)) :
      HolderBound eta (cylinder Set.univ (p0.2-4*h^2) p0.2) (spatialDD (w p0)) MW ∧
      powerBound gamma Csharp (chuOscillation (cylinder Set.univ (p0.2-4*h^2) p0.2) (spatialDD (w p0))) := by
    let l : ℝ := p0.2-4*h^2
    let phi : Space n → ℝ := L16Aux.innerPatchBump h hh p0.1
    let A0 : Sym n := S p0+T (hessian u p0) p0
    have hlr : l < p0.2 := by dsimp only [l]; nlinarith only [sq_pos_of_pos hh]
    have hDur : p0.2-l=4*h^2 := by dsimp only [l]; ring
    have hPatchBig := chuCausalPatch_subset_backward hh.le hhSmall hp0
    have hPatchLow := chuCausalPatch_subset_low_box hh.le hhSmall hp0
    have hPatchOne : cylinder (Metric.ball p0.1 (2*h)) l p0.2 ⊆ backward 1 := hPatchBig.trans hBig
    have hLoE := L16Aux.holderBound_mono hLowEta hPatchLow
    have hLoG := L16Aux.holderBound_mono hLowGamma hPatchLow
    have hHE := L16Aux.holderBound_mono hHcoarse hPatchBig
    have hPhiE := hSpatialEta h hh hh1 p0.1 l p0.2
    have hPhiG := hSpatialGamma h hh hh1 p0.1 l p0.2
    have hThetaE := hTimeEta l p0.2 hlr (by rw [hDur]; exact hDuration)
    have hThetaG := hTimeGamma l p0.2 hlr (by rw [hDur]; exact hDuration)
    rw [hDur] at hThetaE hThetaG
    have hReta := chuFrozenResidual_holderBound hell.le hL hK.le hF hT
      (hRange p0 (hHalfBig hp0)) (hHalfBig hp0) (by norm_num) (by norm_num) hCoarse
    have hRE := L16Aux.holderBound_mono hReta hPatchBig
    have hPhiSmooth : ContDiff ℝ 2 phi := (L16Aux.innerPatchBump_contDiff hh p0.1).of_le (by simp)
    have hSupport : tsupport phi ⊆ Metric.ball p0.1 (2*h) := chu_innerPatchBump_support hh p0.1
    have hUnit : ∀ x, |phi x| ≤ 1 := chu_innerPatchBump_unit hh p0.1
    have hSlope : ‖(chuFrozenSlope hT F A0 p0 (hHalfBig hp0) : Mat n)‖ ≤ Ma := by
      have hs := slopeSet_norm_le (show 0 ≤ ell*K⁻¹ from by positivity)
        (chuFrozenSlope_mem_slopeSet hell.le hL hF hT (hRange p0 (hHalfBig hp0)) (hHalfBig hp0))
      exact hs.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity : (0:ℝ) ≤ 2*n))
    have hEll := chuFrozenSlope_elliptic hell hL hK hF hT (hRange p0 (hHalfBig hp0)) (hHalfBig hp0)
      (cylinder Set.univ l p0.2)
    have hPair := hResidual E U F T S f u hE hF hT hS hDF hf hCoarse hRange hPDE p0 hp0 h hh hhSmall hhRho
    have hHGlobal := chu_cutoff_hessian_coarse_holder Metric.isOpen_ball hPhiSmooth hSupport
      (chu_c2_cylinder_restrict_backward hlr hPatchOne hu) hPhiE.1 hPhiE.2.1 hPhiE.2.2 hLoE hHE hThetaE.1
    refine ⟨hHGlobal,?_⟩
    exact hCutoff T K beta hT F A0 p0 (hHalfBig hp0) (Metric.ball p0.1 (2*h)) l p0.2 eta gamma
      Ma MR M epsilon A e0 e1 e2 ce de de E0 E1 E2 cg dg dg phi u hlr
      (by rw [hDur]; exact hDuration) he he1 hg hg1 Metric.isOpen_ball hPhiSmooth hSupport hPatchOne hu
      hMa heps.le hA hSlope hEll hUnit hPhiE.1 hPhiE.2.1 hPhiE.2.2 hPhiG.1 hPhiG.2.1 hPhiG.2.2
      hLoE hLoG hHE hRE hThetaE.1 hThetaE.2 hThetaG.1 hThetaG.2 hPair hSmallGamma hSmallEta
  have hOrdered (p0 : Point n) (hp0 : p0 ∈ backward (1/2)) (q : Point n) (hq : q ∈ backward (1/2))
      (hTime : q.2 ≤ p0.2) (hNear : parabolicDistance p0 q ≤ h/2) :
      ‖spatialDD u p0-spatialDD u q‖ ≤ Csharp*(parabolicDistance p0 q)^gamma := by
    have hSymm : parabolicDistance q p0=parabolicDistance p0 q := by
      simp only [parabolicDistance,norm_sub_rev,abs_sub_comm]
    by_cases hPos : 0 < parabolicDistance p0 q
    · have hPlateau := chu_near_pair_cutoff_hessian hh u hTime (hSymm ▸ hNear)
      have hqPatch := (chu_near_pair_patch_plateau hh hTime (hSymm ▸ hNear)).1
      have hData := hPatchData p0 hp0
      have hPair := chuOscillation_pair_le hData.1.1 hData.1.2.1
        (p := p0) (q := q) ⟨Set.mem_univ _,by nlinarith only [sq_nonneg h],le_rfl⟩
        ⟨Set.mem_univ _,hqPatch.2⟩ (le_refl (parabolicDistance p0 q))
      rw [hPlateau.1,hPlateau.2] at hPair
      have hd1 : parabolicDistance p0 q ≤ 1 := hNear.trans (by linarith only [hhSmall])
      exact hPair.trans (hData.2 _ ⟨hPos,hd1⟩).2
    · have hd0 : parabolicDistance p0 q=0 := le_antisymm (le_of_not_gt hPos)
        (add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      have hW := holderWeight_le_twice_radius_power he.le (le_refl (parabolicDistance p0 q))
      rw [hd0,Real.zero_rpow he.ne',mul_zero] at hW
      have hz := (hHcoarse.2.2 p0 (hHalf hp0) q (hHalf hq)).trans (mul_le_mul_of_nonneg_left hW hM)
      simp only [mul_zero] at hz
      exact hz.trans (mul_nonneg hCsharp (Real.rpow_nonneg (by rw [hd0]) _))
  have hNear (p : Point n) (hp : p ∈ backward (1/2)) (q : Point n) (hq : q ∈ backward (1/2))
      (hpq : parabolicDistance p q ≤ h/2) :
      ‖spatialDD u p-spatialDD u q‖ ≤ Csharp*(parabolicDistance p q)^gamma := by
    rcases le_total q.2 p.2 with hqp | hpqTime
    · exact hOrdered p hp q hq hqp hpq
    · have hSymm : parabolicDistance q p=parabolicDistance p q := by
        simp only [parabolicDistance,norm_sub_rev,abs_sub_comm]
      have hh := hOrdered q hq p hp hpqTime (by rw [hSymm]; exact hpq)
      rw [norm_sub_rev,hSymm] at hh
      exact hh
  have hFinal := chu_holderBound_of_near_power hg.le hg1.le (by positivity : 0 < h/2) hM hCsharp
    (fun p hp => hHcoarse.2.1 p (hHalf hp)) hNear
  exact L16Aux.holderBound_mono_const hFinal (by dsimp only [Cfinal]; linarith)

end Yau.LeafProofs.L05Aux
