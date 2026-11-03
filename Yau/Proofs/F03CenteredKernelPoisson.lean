import Yau.Proofs.F03CenteredHeatGenerator
import Yau.Proofs.F03TerminalProfileInitialLimit
import Yau.Proofs.F03BoundedInitialFaceProducer

/-! The actual centered unbounded flow potential satisfies the full zero-endpoint Poisson heat identity. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem dirichletMinimalKernel_centered_poisson
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : s ∈ Icc 0 T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {B : ℝ} (hB : 0 < B) (x : Pt X) :
    (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO B x y*
      centeredFlowPotential X U T y s ∂μ)-centeredFlowPotential X U T x s =
      ∫ b in (0:ℝ)..B,∫ y,
        dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*
          laplacian X.metric.form (fun z => centeredFlowPotential X U T z s) y ∂μ := by
  let v : Pt X → ℝ := fun y => centeredFlowPotential X U T y s
  have hv : SmoothFn v := smoothSpaceTime_slice (centeredFlowPotential_smooth X o h U P ρ hf hT) hs
  let f : Pt X → ℝ := laplacian X.metric.form v
  have hfSmooth : SmoothFn f := smoothFn_laplacian X.metric hv
  have hfBound (y : Pt X) : |f y| ≤ (n:ℝ) := centeredFlowPotential_laplacian_bound X o h U P ρ hf hT hs y
  let q : ℝ → ℝ := fun b => ∫ y,
    dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*f y ∂μ
  have hqCont : ContinuousOn q (Ioc 0 B) := by
    intro b hb
    have hClass := dirichletMinimalBoundedHeat_class X.metric X.kahler_metric μ hμ O hO f hfSmooth ⟨n,hfBound⟩
    have hDeriv := hClass.2.2.2 x b hb.1
    have hEq : q =ᶠ[𝓝 b] (fun r => boundedKernelEvolution μ
        (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO) f r x) := by
      filter_upwards [Ioi_mem_nhds hb.1] with r hr
      have hr0 : 0 < r := hr
      simp only [q,boundedKernelEvolution,if_neg hr0.ne']
    exact (hDeriv.continuousAt.congr hEq.symm).continuousWithinAt
  have hFin : (volume : Measure ℝ) (Ioc (0:ℝ) B) ≠ ⊤ :=
    ((measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne
  have hIntQ : IntegrableOn q (Ioc 0 B) volume := by
    apply (show IntegrableOn (fun _ : ℝ => (n:ℝ)) (Ioc 0 B) volume from integrableOn_const hFin).mono'
      (hqCont.aestronglyMeasurable measurableSet_Ioc)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with b hb
    have hBound := (dirichletMinimalKernelCandidate_bounded_evolution_le X.metric X.kahler_metric μ hμ O hO
      f (continuous_of_smoothFn hfSmooth).aestronglyMeasurable n (Nat.cast_nonneg n) hfBound hb.1 x).2
    have hb0 : 0 < b := hb.1
    simpa only [q,Real.norm_eq_abs,boundedKernelEvolution,if_neg hb0.ne'] using hBound
  have hInitial := dirichletMinimalKernel_terminal_profile_initial_limit X o h U P ρ hf hT.le μ hμ O hO
    v (continuous_of_smoothFn hv) (A := 2*T) (by positivity)
    (fun y => ((centeredFlowPotential_terminal_envelope X o h U P ρ hf hT hs y).1).trans
      (by nlinarith)) x
  have hEnd := (dirichletMinimalKernel_centered_heat_hasDerivAt X o h U P ρ hf u hu hT hs μ hμ O hO hB x).continuousAt.tendsto
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hB
    (fun b hb => dirichletMinimalKernel_centered_heat_hasDerivAt X o h U P ρ hf u hu hT hs μ hμ O hO hb.1 x)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hB.le).mpr hIntQ) hInitial
    (hEnd.mono_left nhdsWithin_le_nhds)

end Yau.Proofs.F03Aux
