import Yau.LeafProofs.L05PerturbationIteration
import Yau.LeafProofs.L05PerturbationOriginEstimates
import Yau.LeafProofs.L05PerturbationNormalizationNumbers
import Yau.LeafProofs.L05PerturbationCenteredData
import Yau.LeafProofs.L05PerturbationCenteredTaylor
import Yau.LeafProofs.L05PerturbationCenteredJets

open Filter Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_centered_actual_estimates_of_autonomous
    (hAuto : ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
      ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < C ∧
        ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
          ConcaveOn ℝ univ F → F 0=0 → ∀ u : Point n → ℝ,
          ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p| ≤ 1) →
          viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
          SchauderBound eta (backward (1/2)) u C)
:
  ∀ n : ℕ, 0 < n → ∀ alpha beta ell L M fB uB : ℝ,
    0 < alpha → alpha < 1 → 0 < beta → beta < 1 → 0 < ell → ell ≤ L →
    0 ≤ M → 0 ≤ fB → 0 ≤ uB →
    ∃ eta rstar E Jjet : ℝ,
      0 < eta ∧ eta < min alpha beta ∧ 0 < rstar ∧ rstar ≤ 1/16 ∧
      0 < E ∧ 0 < Jjet ∧
      ∀ (Phi : Sym n → Point n → ℝ) (f u : Point n → ℝ),
      ContinuousOn (fun z : Sym n × Point n => Phi z.1 z.2)
        (Set.univ ×ˢ backward 1) →
      (∀ p ∈ backward 1, globalElliptic (fun H => Phi H p) ell L) →
      (∀ p ∈ backward 1, ConcaveOn ℝ Set.univ (fun H => Phi H p)) →
      (∀ H : Sym n, ∀ p ∈ backward 1, ∀ q ∈ backward 1,
        |Phi H p-Phi H q| ≤ M*(1+‖H‖)*holderWeight beta p q) →
      |Phi 0 (0,0)| ≤ M → HolderBound alpha (backward 1) f fB →
      C2 (backward 1) u → (∀ p ∈ backward 1, |u p| ≤ uB) →
      (∀ p ∈ backward 1,
        timeD (backward 1) u p-Phi (hessian u p) p=f p) →
      ∀ z ∈ backward (3/4),
        (|u z| ≤ Jjet ∧ ‖spatialD u z‖ ≤ Jjet ∧
          ‖spatialDD u z‖ ≤ Jjet ∧ |timeD (backward 1) u z| ≤ Jjet) ∧
        ∀ r : ℝ, 0 < r → r ≤ rstar →
          ∀ p ∈ perturbClosed z.1 r z.2,
            |u p-perturbTaylor (backward 1) u z p| ≤ E*r^(2+eta) := by
  intro n hn alpha beta ell L M fB uB ha ha1 hb hb1 hell hL hM hfb hub
  obtain ⟨eta,rho,K,mu0,af0,he,heAB,hrho,hrhob,hK,hmu,haf,hIteration⟩ :=
    perturb_polynomial_iteration_of_autonomous hAuto n hn ell L alpha beta hell hL ha ha1 hb hb1
  have hrho1 : rho < 1 := lt_of_le_of_lt hrhob (by norm_num)
  let N := 1+2*uB+3*M+fB
  let Q0 := 3*M+fB
  obtain ⟨r0,hr0,hr0b,hN1,hN,hQ0,hNbudget,hMu,hAf⟩ := perturb_normalization_numeric_data ha hb hmu haf hM hfb hub
  let Sb := perturbIterationCoefficientSum rho (1+eta) K
  let SA := perturbIterationCoefficientSum rho eta K
  let Sq := perturbIterationCoefficientSum rho eta K
  let E0 := perturbIterationRemainderBudget rho eta K
  let rstar := r0*rho
  let E := N*E0/r0^(2+eta)
  let Cgrad := (N/r0)*Sb
  let Cdd := (N/r0^2)*SA
  let Cut := (N/r0^2)*Sq
  let Jjet := 1+uB+Cgrad+Cdd+Cut+Q0
  have hSb : 0 < Sb := perturb_iteration_coefficient_sum_pos hrho hrho1 (by linarith) hK
  have hSA : 0 < SA := perturb_iteration_coefficient_sum_pos hrho hrho1 he hK
  have hSq : 0 < Sq := perturb_iteration_coefficient_sum_pos hrho hrho1 he hK
  have hE0 : 0 < E0 := perturb_iteration_remainder_budget_pos hrho hrho1 he hK
  have hGrad0 : 0 ≤ Cgrad := by dsimp only [Cgrad]; positivity
  have hDD0 : 0 ≤ Cdd := by dsimp only [Cdd]; positivity
  have hUt0 : 0 ≤ Cut := by dsimp only [Cut]; positivity
  have hRstar : 0 < rstar := mul_pos hr0 hrho
  have hRstarB : rstar ≤ 1/16 :=
    ((mul_le_mul_of_nonneg_left (hrhob.trans (by norm_num : (1/16 : ℝ) ≤ 1)) hr0.le).trans_eq (mul_one r0)).trans hr0b
  have hE : 0 < E := div_pos (mul_pos hN hE0) (Real.rpow_pos_of_pos hr0 _)
  have hJ : 0 < Jjet := by dsimp only [Jjet]; linarith only [hub,hGrad0,hDD0,hUt0,hQ0]
  refine ⟨eta,rstar,E,Jjet,he,heAB,hRstar,hRstarB,hE,hJ,?_⟩
  intro Phi f u hJoint hEll hConc hCoeff hAnchor hf hu hSup hPDE z hz
  have hBuf := perturb_center_closed_subset hz hr0 hr0b
  let q0 := Phi 0 z+f z
  let v := perturbNormalize u z r0 N q0
  have hNormData := perturb_centered_holder_data hb hM hJoint hEll hConc hCoeff hAnchor hf hu hSup hPDE z
    hr0 (hr0b.trans (by norm_num : (1/16 : ℝ) ≤ 1)) hN1 hNbudget hBuf hMu hAf
  obtain ⟨c,b,A,q,hc0,hb0,hA0,hq0,_,hError,hc,hb',hA,hq,_⟩ :=
    hIteration (perturbCenteredOperator Phi z r0 N) (perturbCenteredSource f z r0 N) v hNormData
  have hV : C2 (backward 1) v := perturb_normalize_c2 hu z hr0 hBuf
  have hActual := perturb_iteration_origin_actual_estimates hrho hrho1 he hK hV c q b A hc0 hb0 hA0 hq0 hc hb' hA hq hError
  have hOrigin : ((0,0) : Point n)∈backward 1 := by norm_num [backward]
  have hzOrig : z∈backward 1 := by simpa only [perturbCenter_zero] using perturb_center_mem_original hr0 hBuf hOrigin
  have hSlope : |q0| ≤ Q0 := perturb_center_zero_slope_bound hb hM hCoeff hAnchor hf hzOrig
  have hPull := perturb_normalized_origin_jet_pullback hu z hr0 hN hBuf hActual.2.1 hActual.2.2.2.1 hActual.2.2.2.2.1 hSlope
  have hUD : ‖spatialD u z‖ ≤ Cgrad := hPull.1
  have hUDD : ‖spatialDD u z‖ ≤ Cdd := hPull.2.1
  have hUt : |timeD (backward 1) u z| ≤ Q0+Cut := hPull.2.2
  have hPhysical : ∀ r : ℝ, 0 < r → r ≤ rstar → ∀ p∈perturbClosed z.1 r z.2,
      |u p-perturbTaylor (backward 1) u z p| ≤ E*r^(2+eta) :=
    perturb_centered_remainder_pullback hu z hr0 hN hBuf q0 hActual.2.2.2.2.2
  have hJDef : Jjet=1+uB+Cgrad+Cdd+Cut+Q0 := rfl
  refine ⟨⟨?_,?_,?_,?_⟩,hPhysical⟩
  · exact (hSup z hzOrig).trans (by linarith only [hJDef,hGrad0,hDD0,hUt0,hQ0])
  · exact hUD.trans (by linarith only [hJDef,hub,hDD0,hUt0,hQ0])
  · exact hUDD.trans (by linarith only [hJDef,hub,hGrad0,hUt0,hQ0])
  · exact hUt.trans (by linarith only [hJDef,hub,hGrad0,hDD0])

end Yau.LeafProofs.L05Aux
