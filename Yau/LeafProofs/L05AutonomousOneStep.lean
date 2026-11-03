import Yau.LeafProofs.L05AutonomousOneStepGeometry
import Yau.LeafProofs.L05AutonomousOneStepProbability
import Yau.LeafProofs.L05AutonomousDeficitHarnack
import Yau.LeafProofs.L05AutonomousSecondUpper
import Yau.LeafProofs.L05AutonomousFiniteContraction
import Yau.LeafProofs.L05AutonomousOscillationDecayEnergy

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
set_option maxHeartbeats 2400000
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Actual canonical Hessian and negative time fields contract on every buffered
backward cylinder. All directions and constants precede the equation and solution. -/
theorem auto_actual_one_step (n : ℕ) (hn : 0<n) (ell L : ℝ)
    (hell : 0<ell) (hL : ell≤L) :
    ∃ N : ℕ, 0<N ∧ ∃ e : Fin N → Space n,
      (∀ j, ‖e j‖=1) ∧
      (∀ H : Sym n, ‖H‖≤(2*n : ℝ)*2*∑ j, |autoBilinearMap n H (e j) (e j)|) ∧
    ∃ theta : ℝ, 0<theta ∧ theta<1 ∧
    ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
      ConcaveOn ℝ univ F → F 0=0 →
    ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) →
      (∀ p∈unitClosed n, |u p|≤1) →
      viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
    ∀ w : Point n →ᵇ ℝ, UniformContinuous (w : Point n → ℝ) →
      EqOn (w : Point n → ℝ) u (unitClosed n) →
    ∀ V : Point n → ℝ, ContinuousOn V (autoClosed (0 : Space n) (15/16) 0) →
      autoPucci ell L (autoOpen (0 : Space n) (15/16) 0) V →
    ∀ B : ℝ, 0≤B → ∀ S : Set (Point n), MeasurableSet S →
      S⊆autoOpen (0 : Space n) (5/8) 0 →
      (∀ᵐ p ∂volume.restrict (autoOpen (0 : Space n) (5/8) 0), p∈S) →
      Measurable (peanoMeasurableHessian w) →
      (∀ p∈S, |V p|≤B) →
      (∀ p∈S, ∀ v : Space n, ‖v‖=1 →
        |autoBilinearMap n (peanoMeasurableHessian w p) v v|≤B) →
      (∀ v : Space n, ‖v‖=1 → ∀ h : ℝ, h≠0 → |h|<1/512 →
        ∀ p∈autoClosed (0 : Space n) (11/16) 0, |autoSecond w v h p|≤B) →
      (∀ p∈S, ∀ v : Space n, Tendsto (fun h : ℝ => autoSecond w v h p)
        (𝓝[>] 0) (𝓝 (autoBilinearMap n (peanoMeasurableHessian w p) v v))) →
      (∀ p∈S, F (peanoMeasurableHessian w p)=V p) →
      (∀ j, Measurable (oneStepFields e w V j)) ∧
      (∀ j, ∀ p∈S, |oneStepFields e w V j p|≤B) ∧
      (∀ c R T, 0<R → R≤1/64 →
        autoClosed c R T⊆autoClosed (0 : Space n) (5/8) 0 →
        (S∩autoClosed c R T).Nonempty) ∧
      (∀ c R T, 0<R → R≤1/64 →
        autoClosed c R T⊆autoClosed (0 : Space n) (5/8) 0 →
        autoJetOsc S (oneStepFields e w V) c (R/8) T ≤
          theta*autoJetOsc S (oneStepFields e w V) c R T) := by
  classical
  obtain ⟨N,hN,e,a,b,ha,hab,he,hFrame,hReconstruct⟩ :=
    auto_finite_positive_directions n hn ell L hell hL
  obtain ⟨p,CH,hp,hp1,hCH,hSecond,hContinuous⟩ :=
    auto_limiting_deficit_harnack_shared hn hell hL
  have ha' : 0 < min a 1 := lt_min ha (by norm_num)
  have hab' : min a 1≤ max b 1 := (min_le_left _ _).trans (hab.trans (le_max_left _ _))
  have hTheta := finite_contraction_constants (m := N+1) (by omega) (p := p) ha' hab' hCH
  refine ⟨N,hN,e,he,?_,finiteContractionTheta (N+1) (min a 1) (max b 1) p CH,
    hTheta.2.1,hTheta.2.2,?_⟩
  · intro H
    simpa only [oneStep_tracePair_bilinear] using hReconstruct H
  intro F hF hE hConc _hF0 u hu _huBound hSol w hw hEq V hV hVPucci
    B hB S _hSMeas hS hFull _hHMeas hVB hHB hDeltaBound hLimit hEquation
  have hBigK : autoClosed (0 : Space n) (5/8) 0⊆autoClosed (0 : Space n) (15/16) 0 :=
    autoClosed_subset 0 (by norm_num) (by norm_num) 0
  have hSBig : S⊆autoClosed (0 : Space n) (5/8) 0 :=
    hS.trans (oneStep_open_subset_closed _ _ _)
  have hFieldsMeas := oneStepFields_measurable e w hV
  have hFieldsBound := oneStepFields_bounded e he w V (hSBig.trans hBigK) hVB hHB
  have hFullOn (c : Space n) {R T : ℝ}
      (hQ : autoClosed c R T⊆autoClosed (0 : Space n) (5/8) 0) :
      ∀ᵐ q ∂volume.restrict (autoOpen c R T), q∈S :=
    oneStep_restrict_full (autoOpen_isOpen _ _ _).measurableSet
      (autoOpen_isOpen _ _ _).measurableSet
      (oneStep_open_of_closed_subset (by norm_num : (5/8 : ℝ)≠0) hQ) hFull
  have hNonempty (c : Space n) {R T : ℝ} (hR : 0<R)
      (hQ : autoClosed c R T⊆autoClosed (0 : Space n) (5/8) 0) :=
    oneStep_good_nonempty c hR (hFullOn c hQ)
  refine ⟨hFieldsMeas,hFieldsBound,(fun c _ _ hR _ hQ => hNonempty c hR hQ),?_⟩
  intro c R T hR _hRsmall hQ
  let fields := oneStepFields e w V
  let Q := S∩autoClosed c R T
  let Qsmall := S∩autoClosed c (R/8) T
  let early := autoEarly c (R/2) T
  let E := S∩early
  let μ := oneStepEarlyProbability c (R/2) T
  have oneStep_actual_early_probability : IsProbabilityMeasure μ :=
    oneStepEarlyProbability_isProbability c (half_pos hR) T
  have hHalfQ : autoClosed c (R/2) T⊆autoClosed c R T :=
    autoClosed_subset c (half_pos hR).le (by linarith only [hR]) T
  have hSmallQ : autoClosed c (R/8) T⊆autoClosed c R T :=
    autoClosed_subset c (by positivity) (by linarith only [hR]) T
  have hEarlyHalf : early⊆autoClosed c (R/2) T :=
    (autoEarly_subset_open c (half_pos hR) T).trans (oneStep_open_subset_closed _ _ _)
  have hEarlyQ : early⊆autoClosed c R T := hEarlyHalf.trans hHalfQ
  have hEarlyBig : early⊆autoOpen (0 : Space n) (5/8) 0 :=
    (autoEarly_subset_open c (half_pos hR) T).trans
      (autoOpen_subset c (half_pos hR).le (by linarith only [hR]) T) |>.trans
      (oneStep_open_of_closed_subset (by norm_num : (5/8 : ℝ)≠0) hQ)
  have hμ : ∀ᵐ q ∂μ, q∈E :=
    oneStepEarlyProbability_good_ae c (R/2) T (autoOpen_isOpen _ _ _).measurableSet hEarlyBig hFull
  have hSmall : Qsmall.Nonempty := hNonempty c (by positivity) (hSmallQ.trans hQ)
  have hSmallSub : Qsmall⊆Q := inter_subset_inter_right S hSmallQ
  have hEQ : E⊆Q := inter_subset_inter_right S hEarlyQ
  have hU (j) : BddAbove (fields j '' Q) :=
    (auto_jet_range_bounded (fields j) (hFieldsBound j)).1
  have hLw (j) : BddBelow (fields j '' Q) :=
    (auto_jet_range_bounded (fields j) (hFieldsBound j)).2
  let M := fun j => finiteFieldSup (fields j) Q
  have hSup (j) (q) (hq : q∈Q) : fields j q≤M j :=
    le_csSup (hU j) (mem_image_of_mem _ hq)
  have hPoint : ∀ j, ∀ z∈Qsmall,
      autoLpMean early p (fun y => M j-fields j y) ≤ CH*(M j-fields j z) := by
    refine Fin.cases ?_ ?_
    · have hTimeEq : EqOn (fields 0) (fun q => -V q)
          (autoClosed (0 : Space n) (15/16) 0) := by
        intro q hq
        exact congrArg Neg.neg (oneStepTimeRep_eq V hq)
      have hTimeC : ContinuousOn (fields 0) (autoClosed c R T) :=
        hV.neg.congr_mono (hTimeEq.mono (hQ.trans hBigK)) (hQ.trans hBigK)
      have hTimeUpper : ∀ q∈autoClosed c R T, fields 0 q≤M 0 :=
        oneStep_continuous_upper c hR (hFullOn c hQ) hTimeC
          (fun q hq => hSup 0 q hq)
      have hOpenHalf : autoOpen c (R/2) T⊆autoOpen (0 : Space n) (15/16) 0 :=
        oneStep_open_of_closed_subset (by norm_num : (15/16 : ℝ)≠0)
          (hHalfQ.trans (hQ.trans hBigK))
      have hTimeSub : viscositySub (autoOpen c (R/2) T)
          (fun H _ => pucciPlus ell L H) (fun _ => 0) (fields 0) :=
        viscositySub_eqOn_open (autoOpen_isOpen _ _ _)
          (hTimeEq.mono ((oneStep_open_subset_closed _ _ _).trans (hHalfQ.trans (hQ.trans hBigK))))
          (viscositySub_mono_domain (oneStep_sub_neg_of_super hVPucci.2) hOpenHalf)
      intro z hz
      exact hContinuous c R T hR (fields 0) (M 0) (hTimeC.mono hHalfQ)
        (fun q hq => hTimeUpper q (hHalfQ hq)) hTimeSub z hz.2
    · intro j z hz
      have hMeas : Measurable (fields j.succ) := hFieldsMeas j.succ
      have hLimAE : ∀ᵐ q ∂volume.restrict (autoOpen c R T),
          Tendsto (fun h : ℝ => autoSecond w (e j) h q) (𝓝[>] 0) (𝓝 (fields j.succ q)) :=
        (hFullOn c hQ).mono (fun q hq => hLimit q hq (e j))
      have hUpperAE : ∀ᵐ q ∂volume.restrict (autoOpen c R T), fields j.succ q≤M j.succ := by
        filter_upwards [hFullOn c hQ,ae_restrict_mem (autoOpen_isOpen c R T).measurableSet] with q hq hqO
        exact hSup j.succ q ⟨hq,oneStep_open_subset_closed _ _ _ hqO⟩
      let steps := autoDeficitDyadic (1/512)
      have hStepsPos (k) : 0<steps k := autoDeficitDyadic_pos (by norm_num) k
      have hStepsSmall (k) : |steps k|<1/512 := autoDeficitDyadic_abs_lt (by norm_num) k
      have hClosedBuffer : autoClosed c R T⊆autoClosed (0 : Space n) (11/16) 0 :=
        hQ.trans (autoClosed_subset 0 (by norm_num) (by norm_num) 0)
      have hFiniteB : ∀ k, ∀ q∈autoOpen c R T, |autoSecond w (e j) (steps k) q|≤B :=
        fun k q hq => hDeltaBound (e j) (he j) (steps k) (hStepsPos k).ne' (hStepsSmall k) q
          (hClosedBuffer (oneStep_open_subset_closed _ _ _ hq))
      have hUpper (h : ℝ) (hh : h≠0) (hhR : |h|<R/4) :
          ∀ q∈autoClosed c (R/2) T, autoSecond w (e j) h q≤M j.succ :=
        auto_second_upper_closed_half c hR T w hw hMeas (e j) (he j).le
        steps hStepsPos ((autoDeficitDyadic_tendsto_right (by norm_num)).mono_right nhdsWithin_le_nhds)
        hB hFiniteB (hLimAE.mono (fun q hq => hq.comp (autoDeficitDyadic_tendsto_right (by norm_num))))
        hUpperAE hh hhR
      have hEarlyLim : ∀ᵐ q ∂volume.restrict early,
          Tendsto (fun h : ℝ => autoSecond w (e j) h q) (𝓝[>] 0) (𝓝 (fields j.succ q)) :=
        (oneStep_restrict_full (autoOpen_isOpen _ _ _).measurableSet
          (autoEarly_isOpen _ _ _).measurableSet hEarlyBig hFull).mono
          (fun q hq => hLimit q hq (e j))
      apply hSecond c R T hR w (fields j.succ) (e j) (M j.succ) B
        (min (R/4) (1/512)) w.continuous hMeas hB (lt_min (by positivity) (by norm_num))
      · intro h hh hhSmall q hq
        exact ⟨hDeltaBound (e j) (he j) h hh (hhSmall.trans_le (min_le_right _ _)) q
          (hClosedBuffer (hHalfQ hq)),hUpper h hh (hhSmall.trans_le (min_le_left _ _)) q hq⟩
      · intro h hh hhSmall
        apply viscositySub_mono_domain
          (oneStep_second_sub hn hell hL hF hE hConc hu hSol w hEq (he j) hh
            (hhSmall.trans_le (min_le_right _ _)))
        exact oneStep_open_of_closed_subset (by norm_num : (3/4 : ℝ)≠0)
          (hHalfQ.trans (hQ.trans (autoClosed_subset 0 (by norm_num) (by norm_num) 0)))
      · exact hEarlyLim
      · exact hz.2
      · exact hLimit z hz.1 (e j)
  have hMean (j) :
      (∫ q, (max (M j-fields j q) 0)^p ∂μ)^(1/p) ≤
        CH*(M j-finiteFieldSup (fields j) Qsmall) := by
    have hIntegral : (∫ q, (max (M j-fields j q) 0)^p ∂μ)=
        ∫ q, (M j-fields j q)^p ∂μ := by
      apply integral_congr_ae
      filter_upwards [hμ] with q hq
      rw [max_eq_left (sub_nonneg.mpr (hSup j q (hEQ hq)))]
    rw [hIntegral]
    change (∫ q, (M j-fields j q)^p ∂oneStepEarlyProbability c (R/2) T)^(1/p)≤_
    rw [oneStepEarlyProbability_lpMean]
    exact oneStep_mean_le_sup_deficit hSmall (fields j) hCH (hPoint j)
  exact finite_oscillation_contraction (N+1) (min a 1) (max b 1) p CH
    (by omega) ha' hab' hp hp1 hCH Qsmall Q E hSmall hSmallSub hEQ μ hμ fields hFieldsMeas hU hLw
    (fun x hx q hq => oneStepFields_positive_secant hell hL e hFrame hE w V
      (hBigK (hSBig hx.1)) (hBigK (hSBig hq.1))
      (hEquation x hx.1) (hEquation q hq.1)) hMean

end Yau.LeafProofs.L05AutonomousAux
