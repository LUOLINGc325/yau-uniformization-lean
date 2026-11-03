import Yau.Proofs.F03CompactChartKernelEnvelope
import Yau.Proofs.F03ProductParameterDerivative
import Yau.Proofs.F03CenteredFlowEnvelope

/-! The actual unbounded centered-potential heat is genuinely C1 on the closed physical slab. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_centered_contDiffOn_one_ball
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b)
    (a : Pt X) (z₀ : ComplexVector n) {r : ℝ} (hr : 0 < r)
    (hKt : Metric.closedBall z₀ r ⊆ chartTarget a) :
    ContDiffOn ℝ 1 (fun p : ComplexVector n × ℝ => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b (chartInv a p.1) y*
        centeredFlowPotential X U T y p.2 ∂μ) (Metric.ball z₀ r ×ˢ Icc 0 T) := by
  let H := dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO
  have hH := dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO
  let S : Set (ComplexVector n × ℝ) := Metric.ball z₀ r ×ˢ Icc 0 T
  let F : (ComplexVector n × ℝ) → Pt X → ℝ := fun p y => H b (chartInv a p.1) y*centeredFlowPotential X U T y p.2
  let D : (ComplexVector n × ℝ) → Pt X → (ComplexVector n × ℝ) →L[ℝ] ℝ := fun p y =>
    spatialTimeProductDerivative (kernelLeftChartDifferential H a b p.1 y)
      (centeredFlowPotential X U T y p.2) (H b (chartInv a p.1) y) (P y p.2-U y T/T)
  obtain ⟨E,hE,hE0,hEnv⟩ := dirichletMinimalKernel_compact_chart_profile_envelope X o h U P ρ hf hT.le
    μ hμ O hO hb a (Metric.closedBall z₀ r) (isCompact_closedBall _ _) hKt
  have hW := centeredFlowPotential_smooth X o h U P ρ hf hT
  have hPoint (p : ComplexVector n × ℝ) (hp : p ∈ S) :
      p.1 ∈ chartTarget a ∧ p.2 ∈ Icc (0:ℝ) T :=
    ⟨hKt (Metric.ball_subset_closedBall hp.1),hp.2⟩
  have hFInt (p : ComplexVector n × ℝ) (hp : p ∈ S) : Integrable (F p) μ := by
    have hFMeas : AEStronglyMeasurable (F p) μ :=
      (kernelSmooth_univ_continuous_right H hH hb (chartInv a p.1)).aestronglyMeasurable.mul
        (continuous_of_smoothFn (smoothSpaceTime_slice hW hp.2)).aestronglyMeasurable
    apply (hE.const_mul (2*T)).mono' hFMeas
    apply ae_of_all μ
    intro y
    have hK0 := dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb (chartInv a p.1) y
    have hBound := (centeredFlowPotential_terminal_envelope X o h U P ρ hf hT hp.2 y).1
    have hDom := (hEnv p.1 (Metric.ball_subset_closedBall hp.1) y).2.1
    change |H b (chartInv a p.1) y*centeredFlowPotential X U T y p.2| ≤ (2*T)*E y
    rw [abs_mul,abs_of_nonneg hK0]
    calc
      _ ≤ H b (chartInv a p.1) y*(2*T*ρ y T) := mul_le_mul_of_nonneg_left hBound hK0
      _ ≤ (2*T)*E y := by
        convert mul_le_mul_of_nonneg_left hDom (by positivity : 0 ≤ 2*T) using 1 <;> ring
  have hDMeas (p : ComplexVector n × ℝ) (hp : p ∈ S) : AEStronglyMeasurable (D p) μ := by
    have hDK := kernelLeftChartDifferential_continuous_right H hH a hb (hPoint p hp).1
    have hK := kernelSmooth_univ_continuous_right H hH hb (chartInv a p.1)
    have hWc := continuous_of_smoothFn (smoothSpaceTime_slice hW hp.2)
    have hPc := continuous_of_smoothFn (smoothSpaceTime_slice hf.2.2.1 hp.2.1)
    have hUT := continuous_of_smoothFn (smoothSpaceTime_slice hf.2.1 hT.le)
    have hCont : Continuous (D p) := by
      dsimp only [D,spatialTimeProductDerivative]
      fun_prop
    exact hCont.aestronglyMeasurable
  have hDBound (y : Pt X) (p : ComplexVector n × ℝ) (hp : p ∈ S) :
      ‖D p y‖ ≤ (2*T+2)*E y := by
    have hWBound := centeredFlowPotential_terminal_envelope X o h U P ρ hf hT hp.2 y
    have hDom := hEnv p.1 (Metric.ball_subset_closedBall hp.1) y
    have hK0 := dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb (chartInv a p.1) y
    calc
      _ ≤ |centeredFlowPotential X U T y p.2| * ‖kernelLeftChartDifferential H a b p.1 y‖+
          |H b (chartInv a p.1) y| * |P y p.2-U y T/T| := spatialTimeProductDerivative_norm_le _ _ _ _
      _ ≤ (2*T*ρ y T)*‖kernelLeftChartDifferential H a b p.1 y‖+H b (chartInv a p.1) y*(2*ρ y T) := by
        rw [abs_of_nonneg hK0]
        exact add_le_add (mul_le_mul_of_nonneg_right hWBound.1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hWBound.2 hK0)
      _ = (2*T)*(‖kernelLeftChartDifferential H a b p.1 y‖*ρ y T)+2*(H b (chartInv a p.1) y*ρ y T) := by ring
      _ ≤ (2*T)*E y+2*E y := add_le_add
        (mul_le_mul_of_nonneg_left hDom.2.2 (by positivity))
        (mul_le_mul_of_nonneg_left hDom.2.1 (by norm_num))
      _ = _ := by ring
  have hDeriv (y : Pt X) (p : ComplexVector n × ℝ) (hp : p ∈ S) :
      HasFDerivWithinAt (fun q => F q y) (D p y) S p := by
    have hSpatial := ((kernelSmooth_univ_smoothFn_left H hH hb y a).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) a).mem_nhds (hPoint p hp).1)).differentiableAt (by simp)
    have hTime := (centeredFlowPotential_hasDerivWithinAt X o h U P ρ hf T y hp.2.1).mono
      (show Icc (0:ℝ) T ⊆ Ici 0 from fun _ ht => ht.1)
    exact (spatialTimeProduct_hasFDerivWithinAt
      (fun z => H b (chartInv a z) y) (centeredFlowPotential X U T y) hSpatial.hasFDerivAt hTime
      (O := chartTarget a)).mono (fun q hq => hPoint q hq)
  have hDCont (y : Pt X) : ContinuousOn (fun p => D p y) S := by
    have hDK : ContinuousOn (fun p : ComplexVector n × ℝ => kernelLeftChartDifferential H a b p.1 y) S :=
      (kernelLeftChartDifferential_smooth_left H hH a hb y).continuousOn.comp continuousOn_fst
        (fun p hp => (hPoint p hp).1)
    have hK : ContinuousOn (fun p : ComplexVector n × ℝ => H b (chartInv a p.1) y) S :=
      (kernelSmooth_univ_smoothFn_left H hH hb y a).continuousOn.comp continuousOn_fst
        (fun p hp => (hPoint p hp).1)
    have hWc : ContinuousOn (fun p : ComplexVector n × ℝ => centeredFlowPotential X U T y p.2) S :=
      (F02Aux.timeSlice_continuousOn hW y).comp continuousOn_snd (fun p hp => hp.2)
    have hPc : ContinuousOn (fun p : ComplexVector n × ℝ => P y p.2-U y T/T) S :=
      ((F02Aux.timeSlice_continuousOn hf.2.2.1 y).comp continuousOn_snd
        (fun p hp => hp.2.1)).sub continuousOn_const
    dsimp only [D,spatialTimeProductDerivative]
    exact (hWc.smul (hDK.clm_comp continuousOn_const)).add
      ((hK.mul hPc).smul continuousOn_const)
  exact contDiffOn_one_integral_of_dominated μ F D ((convex_ball z₀ r).prod (convex_Icc 0 T))
    (((Metric.isOpen_ball : IsOpen (Metric.ball z₀ r)).uniqueDiffOn).prod (uniqueDiffOn_Icc hT))
    (fun y => (2*T+2)*E y) (hE.const_mul (2*T+2))
    (fun y => mul_nonneg (by positivity) (hE0 y)) hFInt hDMeas hDBound hDeriv hDCont

theorem dirichletMinimalKernel_centered_contDiffOn_one
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b) (a : Pt X) :
    ContDiffOn ℝ 1 (fun p : ComplexVector n × ℝ => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b (chartInv a p.1) y*
        centeredFlowPotential X U T y p.2 ∂μ) (chartTarget a ×ˢ Icc 0 T) := by
  intro p hp
  obtain ⟨δ,hδ,hBall⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target (I := ComplexModel n) a) p.1 hp.1
  let r := δ/2
  have hr : 0 < r := half_pos hδ
  have hClosed : Metric.closedBall p.1 r ⊆ chartTarget a := by
    intro z hz
    exact hBall ((Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hδ))
  have hC := dirichletMinimalKernel_centered_contDiffOn_one_ball X o h U P ρ hf hT μ hμ O hO hb a p.1 hr hClosed
  apply (hC p ⟨Metric.mem_ball_self hr,hp.2⟩).mono_of_mem_nhdsWithin
  have hSpace : ∀ᶠ q : ComplexVector n × ℝ in 𝓝[chartTarget a ×ˢ Icc (0:ℝ) T] p,
      q.1 ∈ Metric.ball p.1 r :=
    (continuousAt_fst.eventually (Metric.ball_mem_nhds p.1 hr)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hSpace,self_mem_nhdsWithin] with q hq hqt
  exact ⟨hq,hqt.2⟩

end Yau.Proofs.F03Aux
