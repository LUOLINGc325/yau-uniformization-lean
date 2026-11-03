import Yau.LeafProofs.L05PerturbationFrozenJets
import Yau.LeafProofs.L05PerturbationFrozenResidual
import Yau.LeafProofs.L05PerturbationComparisonGeometry
import Yau.LeafProofs.L05PerturbationCollar
import Yau.LeafProofs.L05PerturbationData
import Yau.LeafProofs.L05PerturbationCoreABP

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_frozen_comparison_of_autonomous
    (hAuto : ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
      ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < C ∧
        ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
          ConcaveOn ℝ univ F → F 0=0 → ∀ u : Point n → ℝ,
          ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p| ≤ 1) →
          viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
          SchauderBound eta (backward (1/2)) u C)
    (n : ℕ) (hn : 0 < n) (ell L : ℝ) (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ nu Cc Cp : ℝ, 0 < nu ∧ nu < 1 ∧ 0 < Cc ∧ 0 < Cp ∧
      ∀ delta : ℝ, 0 ≤ delta → delta ≤ 1 →
      ∀ (Phi : Sym n → Point n → ℝ) (f u : Point n → ℝ),
      perturbSmallData ell L delta Phi f u →
      ∃ h : Point n → ℝ, ContinuousOn h (perturbClosed (0 : Space n) (1/2) 0) ∧
        EqOn h u (perturbBoundary (0 : Space n) (1/2) 0) ∧
        viscositySolution (perturbOpen (0 : Space n) (1/2) 0)
          (fun H _ => Phi H (0,0)) (fun _ => 0) h ∧
        (∀ p∈perturbClosed (0 : Space n) (1/2) 0, |h p| ≤ 1) ∧
        ∀ tau : ℝ, 0 < tau → tau ≤ 1/8 →
          ∀ p∈perturbClosed (0 : Space n) (1/2) 0,
            |u p-h p| ≤ Cc*tau^nu+Cp*delta*(1+tau^(-2 : ℝ)) := by
  obtain ⟨kappa,hk0,hk1,hHolder⟩ := perturb_small_data_holder hn hell hL
  obtain ⟨Cc,hCc,hCollar⟩ := perturb_quantitative_collar n hn ell L kappa 100 hell hL hk0 hk1 (by norm_num)
  obtain ⟨Kh,hKh,hJets⟩ := perturb_frozen_core_jets_of_autonomous hAuto n hn ell L hell hL
  obtain ⟨CABP,hCABP,hABP⟩ := perturb_core_abp n hn ell L hell hL
  let nu := kappa/4
  let Cp := 1+CABP*(2+Kh)
  have hCp : 0 < Cp := by dsimp only [Cp]; positivity
  refine ⟨nu,Cc,Cp,by dsimp only [nu]; positivity,by dsimp only [nu]; linarith,hCc,hCp,?_⟩
  intro delta hd hd1 Phi f u hData
  have hUHolder := hHolder delta hd hd1 Phi f u hData
  rcases hData with ⟨⟨hJoint,hE,hConc,hPhi0,_,hu,hSup,hPDE⟩,hCoeff,hf⟩
  have hOrigin : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  let F := fun H : Sym n => Phi H (0,0)
  have hFOn : ContinuousOn F univ :=
    hJoint.comp (continuous_id.prodMk continuous_const).continuousOn
      (by intro H _; exact ⟨mem_univ _,hOrigin⟩)
  have hF : Continuous F := continuousOn_univ.mp hFOn
  have hFE : globalElliptic F ell L := hE _ hOrigin
  have hFC : ConcaveOn ℝ univ F := hConc _ hOrigin
  have hF0 : F 0=0 := hPhi0
  have hUC : ContinuousOn u (perturbClosed (0 : Space n) (1/2) 0) := hu.1.mono perturb_half_subset_back
  have hUB : ∀ p∈perturbClosed (0 : Space n) (1/2) 0, |u p| ≤ 1 :=
    fun p hp => hSup p (perturb_half_subset_back hp)
  obtain ⟨h,hC,hBoundary,hSol,hBound⟩ := perturb_frozen_half_exists hn hell hL hF hFE hFC hF0
    (by norm_num : (0 : ℝ) ≤ 1) hUC hUB
  have hCollarAll := hCollar F u h hF hFE hF0 hUHolder hC hBoundary hSol
  refine ⟨h,hC,hBoundary,hSol,hBound,?_⟩
  intro tau ht htb p hp
  have hCoreJets := hJets F h hF hFE hFC hF0 hC hBound hSol tau ht htb
  have hOpen : IsOpen (perturbCoreOpen (n := n) tau) := perturbCoreOpen_isOpen tau
  have hOC := perturb_core_open_subset_core (n := n) tau
  have hOB := perturb_core_open_subset_original (n := n) ht.le
  have hhOpen := c2_open_restrict hOpen hOC hCoreJets.1
  have hHeq : ∀ q∈perturbCoreOpen tau, timeD (perturbCoreOpen tau) h q=Phi (hessian h q) (0,0) := by
    intro q hq
    exact (timeD_open_restrict hOpen hOC h hq).trans (hCoreJets.2.2 q (hOC hq))
  have hResidual := perturb_frozen_difference_residual hOpen hOB hell.le hL hd hE hu hhOpen hPDE hHeq hCoeff hf
    (fun q hq => hCoreJets.2.1 q (hOC hq))
  let G := delta*(2+Kh*tau^(-2 : ℝ))
  let E := Cc*tau^nu
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hUCore : ContinuousOn u (perturbCore tau) :=
    hUC.mono (perturbCore_subset_closed ht.le)
  have hHCore : ContinuousOn h (perturbCore tau) :=
    hC.mono (perturbCore_subset_closed ht.le)
  have hBoundaryAbs : ∀ q∈perturbCoreBoundary tau, |u q-h q| ≤ E := by
    intro q hq
    exact hCollarAll tau ht htb q (perturb_core_boundary_subset_collar ht.le htb hq)
  have hUpper := hABP tau G E (fun q => u q-h q) ht htb hG (hUCore.sub hHCore)
    (fun q hq => (abs_le.mp (hBoundaryAbs q hq)).2) hResidual.1
  have hLower := hABP tau G E (fun q => h q-u q) ht htb hG (hHCore.sub hUCore)
    (by intro q hq; have hh := (abs_le.mp (hBoundaryAbs q hq)).1; linarith only [hh]) hResidual.2
  have hForce := perturb_comparison_budget hCABP.le hKh.le hd (Real.rpow_nonneg ht.le (-2 : ℝ))
  change CABP*G ≤ Cp*delta*(1+tau^(-2 : ℝ)) at hForce
  rcases perturb_closed_core_or_collar tau hp with hpCore | hpCollar
  · have hAbs : |u p-h p| ≤ E+CABP*G := by
      apply abs_le.mpr
      exact ⟨by have hh := hLower p hpCore; linarith only [hh],hUpper p hpCore⟩
    exact hAbs.trans (by change E+CABP*G ≤ E+Cp*delta*(1+tau^(-2 : ℝ)); linarith only [hForce])
  · have hAbs := hCollarAll tau ht htb p hpCollar
    have hExtra : 0 ≤ Cp*delta*(1+tau^(-2 : ℝ)) := by positivity
    exact hAbs.trans (by linarith only [hExtra])

end Yau.LeafProofs.L05Aux
