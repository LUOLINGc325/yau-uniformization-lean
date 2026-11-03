import Yau.Proofs.P06CylinderRegularitySmallTime
import Yau.Proofs.P06CylinderRegularityDifferenceRealization
import Yau.Proofs.P06InitialTraceAssembly
import Yau.Proofs.P06RemoteCutoffData

/-! The actual canonical cutoff family satisfies the remote spatial-jet
bounds needed for the original complete smooth initial trace. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.Parabolic Yau.LeafProofs.L03

theorem canonicalCutoff_remoteJetBounds {n k : ℕ} (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (A : RealForm X.manifold k) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B^2)
    (Us : ℕ → ℝ → RealForm X.manifold k)
    (hUs : CanonicalCutoffHeat X.metric μ hμ o χ hχ A hA Us) :
    InitialTrace.RemoteJetBounds (CutoffTail.cutoffForm χ A) A Us := by
  classical
  intro x K hK hKChart m I
  obtain ⟨O,hO,hKO,hOChart,hcO⟩ := exists_open_between_and_isCompact_closure hK
    (isOpen_extChartAt_target (I := ComplexModel n) x) hKChart
  obtain ⟨F,hF,CS,hCS,hKF,hST⟩ := exists_small_time_form_jet_constant X.metric μ hμ x
    hO hcO hOChart hK hKO I m
  have hAbs : ∀ y, formNormSq X.metric.form A y ≤ |B|^2 := by
    intro y
    simpa only [sq_abs] using hb y
  obtain ⟨R,hR,J,hJ,CG,hCG,a,ha,hFR,hPlateau,hGT⟩ :=
    RemoteCutoff.exists_remote_cutoff_data X μ hμ o χ hχ A hA |B| (abs_nonneg B) hAbs F hF
  refine ⟨J,J,3*(m+2*n+1),a,CS*CG,1,hJ,hJ,ha,mul_nonneg hCS.le hCG,zero_lt_one,?_,?_⟩
  · intro z hz
    exact cutoff_component_germ_of_ball_plateau X.metric o χ A J R hPlateau x (hKChart hz)
      (hFR (hKF (Set.mem_image_of_mem (chartInv x) hz))) I
  · intro l hl t ht ht1 z hz
    let D : ℝ → RealForm X.manifold k := fun s => Us l s-Us J s
    have hDs : SmoothFormTime D (Set.Ioi 0) := smoothFormTime_sub (hUs l).2.1 (hUs J).2.1
    have hDPDE : FormHeatEquation X.metric.form D := formHeatEquation_sub X.metric μ hμ
      (hUs l).2.1 (hUs J).2.1 (hUs l).2.2.1 (hUs J).2.2.1
    have hRep (s : ℝ) (hs : s ∈ Set.Ioo (t/4) (2*t)) :
        ∃ hD : L2RealForm X.metric.form μ (D s), realizeActualForm X.metric μ (D s) hD =
          hodgeHeatHilbert X.metric μ hμ k s
            (CutoffTail.cutoffDatum X.metric μ hμ o χ hχ A hA l-
              CutoffTail.cutoffDatum X.metric μ hμ o χ hχ A hA J) :=
      canonicalCutoff_difference_realization X.metric μ hμ o χ hχ A hA Us hUs J l s
        ((by positivity : 0 < t/4).trans hs.1)
    choose hDL hDR using hRep
    let L := CG*Real.exp (-a/t)
    have hL : 0 ≤ L := mul_nonneg hCG (Real.exp_pos _).le
    have hBound : ∀ s (hs : s ∈ Set.Ioo (t/4) (2*t)),
        ‖Davies.indicator X.metric μ F hF.isClosed.measurableSet
          (realizeActualForm X.metric μ (D s) (hDL s hs))‖ ≤ L := by
      intro s hs
      rw [hDR s hs]
      exact hGT l hl t ht ht1.le s ((by positivity : 0 < t/4).trans hs.1) hs.2.le
    have hEst := hST t ht ht1.le D hDs hDPDE hDL L hL hBound z hz t ⟨by linarith,by linarith⟩
    have hS : IsOpen (chartTarget x ×ˢ Set.Ioi (0 : ℝ)) :=
      (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioi
    have hSpatial := InitialTrace.spatial_jet_norm_le_joint_jet hS
      ((hUs l).2.1 x I |>.sub ((hUs J).2.1 x I)) ⟨hKChart hz,ht⟩ m
    change ‖iteratedFDeriv ℝ m (fun w => formComponents (Us l t) x w I-
      formComponents (Us J t) x w I) z‖ ≤ _ at hSpatial
    change ‖iteratedFDeriv ℝ m (fun p : Point n => formComponents (Us l p.2) x p.1 I-
      formComponents (Us J p.2) x p.1 I) (z,t)‖ ≤ _ at hEst
    exact hSpatial.trans (hEst.trans_eq (by dsimp [L]; ring))

end Yau.NodeProofs.P06Aux.CylinderReg
