import Yau.LeafProofs.L05PerturbationComparison
import Yau.LeafProofs.L05PerturbationFrozenCentral
import Yau.LeafProofs.L05PerturbationImprovementParameters

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_one_step_of_autonomous
    (hAuto : ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
      ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < C ∧
        ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
          ConcaveOn ℝ univ F → F 0=0 → ∀ u : Point n → ℝ,
          ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p| ≤ 1) →
          viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
          SchauderBound eta (backward (1/2)) u C)
    (n : ℕ) (hn : 0< n) (ell L alpha beta : ℝ)
    (hell : 0< ell) (hL : ell≤ L)
    (ha : 0< alpha) (ha1 : alpha< 1) (hb : 0< beta) (hb1 : beta< 1) :
    ∃ eta rho delta K : ℝ,
      0< eta ∧ eta< min alpha beta ∧ 0< rho ∧ rho≤ 1/16 ∧
      0< delta ∧ delta≤ 1 ∧ 0< K ∧
      ∀ (Phi : Sym n → Point n → ℝ) (f u : Point n → ℝ),
        perturbSmallData ell L delta Phi f u →
        ∃ (c : ℝ) (b : Space n →L[ℝ] ℝ) (A : Sym n) (q : ℝ),
          |c|≤ K ∧ ‖b‖≤ K ∧ ‖A‖≤ K ∧ |q|≤ K ∧
          q=Phi A (0,0) ∧
          ∀ p ∈ perturbClosed (0 : Space n) rho 0,
            |u p-perturbPolynomial c b A q p|≤ rho^(2+eta) := by
  obtain ⟨nu,Cc,Cp,hn0,hn1,hCc,hCp,hComparison⟩ := perturb_frozen_comparison_of_autonomous hAuto n hn ell L hell hL
  obtain ⟨sigma,K,hs0,hs1,hK1,hCentral⟩ := perturb_frozen_central_schauder_of_autonomous hAuto n hn ell L hell hL
  have hK : 0 < K := lt_trans zero_lt_one hK1
  obtain ⟨eta,rho,tau,delta,he,heAB,heS,hr,hrb,ht,htb,hd,hd1,hSmallR,hSmallT,hSmallD⟩ :=
    perturb_improvement_parameters hs0 ha hb hn0 hCc hCp hK
  refine ⟨eta,rho,delta,K,he,heAB,hr,hrb,hd,hd1,hK,?_⟩
  intro Phi f u hData
  obtain ⟨h,hC,hBoundary,hSol,hSup,hError⟩ := hComparison delta hd.le hd1 Phi f u hData
  rcases hData.1 with ⟨hJoint,hE,hConc,hPhi0,_,_,_,_⟩
  have hOrigin : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  let F := fun H : Sym n => Phi H (0,0)
  have hFOn : ContinuousOn F univ :=
    hJoint.comp (continuous_id.prodMk continuous_const).continuousOn
      (by intro H _; exact ⟨mem_univ _,hOrigin⟩)
  have hF : Continuous F := continuousOn_univ.mp hFOn
  have hFE : globalElliptic F ell L := hE _ hOrigin
  have hFC : ConcaveOn ℝ univ F := hConc _ hOrigin
  have hF0 : F 0=0 := hPhi0
  obtain ⟨hSch,hc,hb',hA,hq,hCompat,hTaylor⟩ := hCentral F h hF hFE hFC hF0 hC hSup hSol
  refine ⟨h (0,0),spatialD h (0,0),hessian h (0,0),timeD (backward (1/4)) h (0,0),hc,hb',hA,hq,hCompat,?_⟩
  intro p hp
  have hpHalf : p∈perturbClosed (0 : Space n) (1/2) 0 :=
    perturb_closed_subset_radius (0 : Space n) hr.le (hrb.trans (by norm_num)) 0 hp
  have hComp := hError tau ht htb p hpHalf
  have hTaylorError := hTaylor rho hr (hrb.trans (by norm_num)) p hp
  have hPower : rho^(2+sigma)=rho^(2+eta)*rho^(sigma-eta) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hTaylorBudget : 3*K*rho^(2+sigma) ≤ rho^(2+eta)/2 := by
    rw [hPower]
    have hh := mul_le_mul_of_nonneg_left hSmallR (Real.rpow_nonneg hr.le (2+eta))
    nlinarith only [hh]
  have hCompareBudget : Cc*tau^nu+Cp*delta*(1+tau^(-2 : ℝ)) ≤ rho^(2+eta)/2 := by
    linarith only [hSmallT,hSmallD]
  have hTri := abs_sub_le (u p) (h p) (perturbPolynomial (h (0,0)) (spatialD h (0,0)) (hessian h (0,0))
    (timeD (backward (1/4)) h (0,0)) p)
  nlinarith only [hTri,hComp,hTaylorError,hTaylorBudget,hCompareBudget]

end Yau.LeafProofs.L05Aux
