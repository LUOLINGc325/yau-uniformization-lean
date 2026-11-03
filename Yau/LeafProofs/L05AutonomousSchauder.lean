import Yau.LeafProofs.L05AutonomousSchauderReconstruction
import Yau.LeafProofs.L05AutonomousMeasurableJet
import Yau.LeafProofs.L05AutonomousOneStep
import Yau.LeafProofs.L05AutonomousOscillationDecay
import Yau.LeafProofs.L05AutonomousHessianRepresentative
import Yau.LeafProofs.L05AutonomousHolderReconstruction

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic Yau.LeafProofs.L05AutonomousAux
local instance autoOriginalSchauder_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance autoOriginalSchauder_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance autoOriginalSchauder_bilinearGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance autoOriginalSchauder_bilinearSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

/-- The exact normalized autonomous concave viscosity Schauder theorem.
All constants precede the equation and continuous solution; the conclusion
uses actual spatial Frechet and within-time derivatives, including time zero. -/
theorem autonomous_concave_schauder (n : ℕ) (hn : 0 < n) (ell L : ℝ)
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < C ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
        ConcaveOn ℝ univ F → F 0=0 →
      ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) →
        (∀ p∈unitClosed n, |u p| ≤ 1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
        SchauderBound eta (backward (1/2)) u C := by
  obtain ⟨N,hN,e,he,hRecon,theta,ht0,ht1,hStep⟩ := auto_actual_one_step n hn ell L hell hL
  obtain ⟨eta,CO,heta,heta1,hCO,hDecay⟩ :=
    auto_contraction_to_holder n (N+1) (by omega) theta ht0 ht1
  obtain ⟨delta,B,hd,hd1,hB,hOriginal⟩ := auto_original_measurable_jet_data n hn ell L hell hL
  have hRawRecon : ∀ H : Sym n, ‖(H : Mat n)‖ ≤
      (2*n : ℝ)*2*∑ j, |autoBilinearMap n H (e j) (e j)| :=
    auto_hessian_frobenius_reconstruction (e := e) hRecon
  obtain ⟨CR,hCR,hRepresentative⟩ := auto_hessian_representative n N e hRawRecon
  let Ldir : ℝ := (2*n : ℝ)*2*(N : ℝ)
  have hLdir : 0 ≤ Ldir := by dsimp only [Ldir];positivity
  let K : ℝ := CO*B
  have hK : 0 ≤ K := mul_nonneg hCO.le hB.le
  let Brep : ℝ := (1+Ldir)*B
  have hBrep : 0 ≤ Brep := mul_nonneg (by positivity) hB.le
  let MH : ℝ := CR*(Brep+K)
  let MV : ℝ := B+K
  have hMH : 0 ≤ MH := mul_nonneg hCR.le (add_nonneg hBrep hK)
  have hMV : 0 ≤ MV := add_nonneg hB.le hK
  obtain ⟨C,hC,hAnalytic⟩ := auto_schauder_from_actual_directional_limits n eta B MH MV
    heta heta1 hB.le hMH hMV
  refine ⟨eta,C,heta,heta1,hC,?_⟩
  intro F hF hE hConc h0 u hu hb hsol
  obtain ⟨w,hwu,hw,hcw,hw1,hMoll,hFinite,V,hVC,hVB,hVdelta,hVPucci,hVTime,hVtimeD,hHMeas,
    S,hSMeas,hS,hFull,hSPeano,hSNorm,hSQuad,hSLimit,hEquation⟩ :=
    hOriginal F hF hE hConc h0 u hu hb hsol
  have hSV : ∀ p∈S, |V p| ≤ B := by
    intro p hp
    exact hVB p ((autoClosed_subset (r := (5/8 : ℝ)) (R := 15/16) 0 (by norm_num) (by norm_num) 0)
      (oneStep_open_subset_closed _ _ _ (hS hp)))
  obtain ⟨hFieldsMeas,hFieldsBound,hNonempty,hContract⟩ :=
    hStep F hF hE hConc h0 u hu hb hsol w hw hwu V hVC hVPucci B hB.le S hSMeas hS hFull
      hHMeas hSV hSQuad hFinite hSLimit hEquation
  have hFieldsPair := hDecay S hS B hB.le (oneStepFields e w V) hFieldsBound hNonempty hContract
  let S9 := S ∩ autoOpen (0 : Space n) (9/16) 0
  have hS9 : S9 ⊆ autoOpen (0 : Space n) (9/16) 0 := inter_subset_right
  have hS9Closed : S9 ⊆ autoClosed (0 : Space n) (9/16) 0 :=
    hS9.trans (oneStep_open_subset_closed _ _ _)
  have hOpen9 : autoOpen (0 : Space n) (9/16) 0 ⊆ autoOpen (0 : Space n) (5/8) 0 :=
    autoOpen_subset 0 (by norm_num) (by norm_num) 0
  have hFull9 : ∀ᵐ p ∂volume.restrict (autoOpen (0 : Space n) (9/16) 0), p∈S9 := by
    filter_upwards [oneStep_restrict_full (autoOpen_isOpen _ _ _).measurableSet
      (autoOpen_isOpen _ _ _).measurableSet hOpen9 hFull,
      ae_restrict_mem (autoOpen_isOpen (0 : Space n) (9/16 : ℝ) 0).measurableSet] with p hp hq
    exact ⟨hp,hq⟩
  have hDir : ∀ j, ∀ p∈S9, ∀ q∈S9,
      |autoBilinearMap n (peanoMeasurableHessian w p) (e j) (e j)-
        autoBilinearMap n (peanoMeasurableHessian w q) (e j) (e j)| ≤ K*holderWeight eta p q := by
    intro j p hp q hq
    simpa only [oneStepFields,Fin.cases_succ] using
      hFieldsPair j.succ p ⟨hp.1,hS9Closed hp⟩ q ⟨hq.1,hS9Closed hq⟩
  have hRawBound : ∀ p∈S9, ‖(peanoMeasurableHessian w p : Mat n)‖ ≤ Brep := by
    intro p hp
    have hSum : (∑ j, |autoBilinearMap n (peanoMeasurableHessian w p) (e j) (e j)|) ≤ (N : ℝ)*B := by
      calc
        _ ≤ ∑ _j : Fin N, B := Finset.sum_le_sum fun j _ => hSQuad p hp.1 (e j) (he j)
        _ = _ := by simp
    calc
      _ ≤ (2*n : ℝ)*2*∑ j, |autoBilinearMap n (peanoMeasurableHessian w p) (e j) (e j)| := hRawRecon _
      _ ≤ (2*n : ℝ)*2*((N : ℝ)*B) := mul_le_mul_of_nonneg_left hSum (by positivity)
      _ = Ldir*B := by dsimp only [Ldir];ring
      _ ≤ Brep := by dsimp only [Brep];nlinarith only [hB.le]
  obtain ⟨Hbar,HB,hHbarC,hHbarEq,hHbarNorm,hHbarPair,hHBMeas,hHBC,hHBSym,hHBMap,hHBNorm,hHBPair⟩ :=
    hRepresentative eta Brep K heta hBrep hK (peanoMeasurableHessian w) S9 hS9 hFull9 hRawBound hDir
  have hHBsmall : HolderBound eta (autoClosed (0 : Space n) (9/16) 0) HB MH := by
    have hSup : CR*Brep ≤ MH := by dsimp only [MH];nlinarith only [hCR.le,hK]
    have hPair : CR*K ≤ MH := by dsimp only [MH];nlinarith only [hCR.le,hBrep]
    refine ⟨hMH,fun p _ => (hHBNorm p).trans hSup,?_⟩
    intro p hp q hq
    exact (hHBPair p hp q hq).trans (mul_le_mul_of_nonneg_right hPair
      (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)))
  have h915 : autoClosed (0 : Space n) (9/16) 0 ⊆ autoClosed (0 : Space n) (15/16) 0 :=
    autoClosed_subset 0 (by norm_num) (by norm_num) 0
  have hVPair9 : ∀ p∈S9, ∀ q∈S9, ‖V p-V q‖ ≤ K*holderWeight eta p q := by
    intro p hp q hq
    have hh := hFieldsPair 0 p ⟨hp.1,hS9Closed hp⟩ q ⟨hq.1,hS9Closed hq⟩
    have hNeg : -V p-(-V q)= -(V p-V q) := by ring
    simpa only [oneStepFields,Fin.cases_zero,oneStepTimeRep_eq V (h915 (hS9Closed hp)),
      oneStepTimeRep_eq V (h915 (hS9Closed hq)),hNeg,abs_neg,Real.norm_eq_abs] using hh
  obtain ⟨hVNorm9,hVHolder9⟩ := auto_continuous_holder_on_full_cylinder
    (0 : Space n) (by norm_num : (0 : ℝ)<9/16) hS9 hFull9 heta hK hB.le V (hVC.mono h915)
    (fun p hp => by simpa only [Real.norm_eq_abs] using hSV p hp.1) hVPair9
  have hVsmall : HolderBound eta (autoClosed (0 : Space n) (9/16) 0) V MV := by
    refine ⟨hMV,fun p hp => (hVNorm9 p hp).trans (by dsimp only [MV];linarith only [hK]),?_⟩
    intro p hp q hq
    exact (hVHolder9 p hp q hq).trans (mul_le_mul_of_nonneg_right
      (show K ≤ MV by dsimp only [MV];linarith only [hB.le])
      (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)))
  have hHBgood : ∀ p∈S9, HB p=autoBilinearMap n (peanoMeasurableHessian w p) := by
    intro p hp
    rw [hHBMap p (hS9Closed hp),hHbarEq hp]
  have hLimitHB : ∀ e : Space n, ‖e‖=1 →
      ∀ᵐ p ∂volume.restrict (autoOpen (0 : Space n) (9/16) 0),
        Tendsto (fun h : ℝ => autoSecond w e h p) (𝓝[>] 0) (𝓝 (HB p e e)) := by
    intro v _hv
    filter_upwards [hFull9] with p hp
    rw [hHBgood p hp]
    exact hSLimit p hp.1 v
  exact hAnalytic w hw hw1 u hwu hu hb hMoll hFinite HB hHBMeas hHBC hHBSym hHBsmall hLimitHB
    V hVC hVsmall (fun x hx a ha b hb => (hVTime x hx).2.2 a ha b hb)

end Yau.LeafProofs.L05Aux
