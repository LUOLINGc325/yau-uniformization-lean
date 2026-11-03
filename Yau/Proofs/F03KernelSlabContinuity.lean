import Yau.Proofs.F03KernelTerminalDomination
import Yau.Proofs.F03CenteredFlowEnvelope

/-! Actual Gaussian domination gives joint continuity of the unbounded potential heat data on the closed physical-time slab. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem dirichletMinimalKernel_terminal_profile_slab_continuous
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b)
    (F : STF X) (hF : SmoothSpaceTime F (Icc 0 T)) {A : ℝ} (hA : 0 ≤ A)
    (hEnvelope : ∀ y s,s ∈ Icc 0 T → |F y s| ≤ A*ρ y T) :
    Continuous (fun p : Pt X × Icc (0:ℝ) T => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b p.1 y*F y p.2.val ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  let L := max 1 (Real.sqrt b)
  have hL : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hbL : b ≤ L^2 := by
    have hh : Real.sqrt b ≤ L := le_max_right _ _
    nlinarith [Real.sq_sqrt hb.le,Real.sqrt_nonneg b]
  let C₀ := (inducedDistance X.metric.form o p₀.1+1)/L
  have hC₀ : 0 ≤ C₀ := div_nonneg (by linarith [X.metric.induced_distance_nonneg o p₀.1]) hL0.le
  have hNear : ∀ᶠ p : Pt X × Icc (0:ℝ) T in 𝓝 p₀,
      inducedDistance X.metric.form o p.1 ≤ C₀*L := by
    have hStrict : inducedDistance X.metric.form o p₀.1 < C₀*L := by
      dsimp [C₀]
      rw [div_mul_cancel₀ _ hL0.ne']
      linarith
    exact (((LeafProofs.L12Aux.continuous_distFrom X.metric o).comp continuous_fst).continuousAt.eventually
      (gt_mem_nhds hStrict)).mono (fun p hp => hp.le)
  obtain ⟨K,c,hK,hc,hKernel⟩ := dirichletMinimalKernelCandidate_coarse_gaussian X o h U P ρ hf C₀ hC₀
  let R := (C₀+1)*L
  have hR : 1 ≤ R := by dsimp [R];nlinarith
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hV : 0 < (μ (distBall X.metric.form o R)).toReal := ENNReal.toReal_pos
    (riemannianVolume_distBall_pos X.metric μ hμ o hR0).ne'
    (riemannianVolume_distBall_lt_top X.metric μ hμ o hR0).ne
  let B := K*(L/Real.sqrt b)^(2*n)/(μ (distBall X.metric.form o R)).toReal
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hDom := (localizedFlow_terminal_density_gaussian_integrable X o h U P ρ hf hT μ hμ hc hR).const_mul (B*A)
  apply continuousAt_of_dominated (bound := fun y => B*A*(Real.exp (-c*(inducedDistance X.metric.form o y/R)^2)*ρ y T))
  · exact Eventually.of_forall (fun p =>
      (kernelSmooth_univ_continuous_right _
        (dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO) hb p.1).aestronglyMeasurable.mul
      (continuous_of_smoothFn (LeafProofs.L19Aux.smoothSpaceTime_slice hF p.2.property)).aestronglyMeasurable)
  · filter_upwards [hNear] with p hp
    apply ae_of_all μ
    intro y
    have hH0 := dirichletMinimalKernelCandidate_nonneg X.metric X.kahler_metric μ hμ O hO hb p.1 y
    have hρ0 := (hf.2.2.2.2.2.2.2.2.2.1 y T hT).2
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hH0]
    calc
      _ ≤ dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b p.1 y*(A*ρ y T) :=
        mul_le_mul_of_nonneg_left (hEnvelope y p.2.val p.2.property) hH0
      _ ≤ _ := by
        convert mul_le_mul_of_nonneg_right (hKernel μ hμ O hO L hL b hb hbL p.1 hp y)
          (mul_nonneg hA hρ0) using 1 <;> dsimp [B,R] <;> ring
  · exact hDom
  · apply ae_of_all μ
    intro y
    have hHCont := kernelSmooth_univ_continuous_left _
      (dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO) hb y
    have hTime := F02Aux.timeSlice_continuousOn hF y
    exact ((hHCont.comp continuous_fst).mul
      ((continuousOn_iff_continuous_restrict.mp hTime).comp continuous_snd)).continuousAt

theorem dirichletMinimalKernel_P_slab_continuous
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b) :
    Continuous (fun p : Pt X × Icc (0:ℝ) T => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b p.1 y*P y p.2.val ∂μ) := by
  apply dirichletMinimalKernel_terminal_profile_slab_continuous X o h U P ρ hf hT μ hμ O hO hb P
    (fun a => (hf.2.2.1 a).mono (fun p hp => ⟨hp.1,hp.2.1⟩)) (A := 1) zero_le_one
  intro y s hs
  simpa only [one_mul] using (localizedFlow_potential_time_envelope X o h U P ρ hf hs y).1

theorem dirichletMinimalKernel_U_slab_continuous
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 ≤ T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b) :
    Continuous (fun p : Pt X × Icc (0:ℝ) T => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b p.1 y*U y p.2.val ∂μ) := by
  apply dirichletMinimalKernel_terminal_profile_slab_continuous X o h U P ρ hf hT μ hμ O hO hb U
    (fun a => (hf.2.1 a).mono (fun p hp => ⟨hp.1,hp.2.1⟩)) (A := T) hT
  exact fun y s hs => (localizedFlow_potential_time_envelope X o h U P ρ hf hs y).2

theorem dirichletMinimalKernel_centered_slab_continuous
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b) :
    Continuous (fun p : Pt X × Icc (0:ℝ) T => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b p.1 y*
        centeredFlowPotential X U T y p.2.val ∂μ) := by
  apply dirichletMinimalKernel_terminal_profile_slab_continuous X o h U P ρ hf hT.le μ hμ O hO hb
    (centeredFlowPotential X U T) (centeredFlowPotential_smooth X o h U P ρ hf hT)
    (A := 2*T) (by positivity)
  exact fun y s hs => (centeredFlowPotential_terminal_envelope X o h U P ρ hf hT hs y).1

end Yau.Proofs.F03Aux
