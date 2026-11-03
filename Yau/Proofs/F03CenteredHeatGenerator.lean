import Yau.Proofs.F03CutoffGreenUniformLimit
import Yau.Proofs.F03KernelPoissonEnvelope
import Yau.Proofs.F03CompactKernelGenerator
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! The actual unbounded centered potential satisfies the genuine heat generator identity. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Yau.Proofs.F03Aux
open Yau Blueprint F02Aux HeatConcreteBindings HeatTargetCandidates LeafProofs.L18Aux LeafProofs.L19Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

theorem dirichletMinimalKernel_centered_heat_hasDerivAt
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {T : ℝ} (hT : 0 < T) {s : ℝ} (hs : s ∈ Icc 0 T)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O) {b : ℝ} (hb : 0 < b) (x : Pt X) :
    HasDerivAt (fun r => ∫ y,
      dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO r x y*
        centeredFlowPotential X U T y s ∂μ)
      (∫ y,dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO b x y*
        laplacian X.metric.form (fun z => centeredFlowPotential X U T z s) y ∂μ) b := by
  obtain ⟨C,hC,hControl⟩ := hu.2.2.2
  let A := max 1 C
  have hA : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hCA : C ≤ A := le_max_right _ _
  let ε := b/2
  let B := b+1
  have hε : 0 < ε := half_pos hb
  have hεB : ε ≤ B := by dsimp [ε,B];linarith
  have hbS : b ∈ Ioo ε B := by dsimp [ε,B];constructor <;> linarith
  let v : Pt X → ℝ := fun y => centeredFlowPotential X U T y s
  have hv : SmoothFn v := smoothSpaceTime_slice (centeredFlowPotential_smooth X o h U P ρ hf hT) hs
  let k : ℝ → Pt X → ℝ := fun r y =>
    dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO r x y
  have hk (r : ℝ) (hr : r ∈ Icc ε B) : SmoothFn (k r) :=
    kernelSmooth_univ_smoothFn_right _
      (dirichletMinimalKernelCandidate_joint_smooth X.metric X.kahler_metric μ hμ O hO) (hε.trans_le hr.1) x
  obtain ⟨E,hE,hE0,hEnvelope⟩ := dirichletMinimalKernel_centered_poisson_envelope
    X o h U P ρ hf hT μ hμ O hO hε hεB x
  have hUniform := exhaustionCutoff_green_generators_tendstoUniformlyOn X o u hu hC
    (fun y => (hControl y).1) (fun y => (hControl y).2.1) hCA hA μ hμ v hv (Icc ε B)
    k hk E hE hE0 (fun r hr y => hEnvelope r hr s hs y)
  let c : ℕ → ScalarEnergyDomain X.metric μ hμ := fun j =>
    ⟨(fun y => exhaustionCutoff u A ((j:ℝ)+1) y*v y),
      smoothFn_mul (exhaustionCutoff_smooth hu.1 A ((j:ℝ)+1)) hv,
      (exhaustionCutoff_compact X o u hu hA0 (by positivity)).mul_right⟩
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo
    (hUniform.mono Ioo_subset_Icc_self)
    (Eventually.of_forall (fun j r hr =>
      dirichletMinimalKernel_compact_hasDerivAt X.metric X.kahler_metric μ hμ O hO (c j)
        (hε.trans hr.1) x))
    (fun r hr => ?_) hbS
  have hInt : Integrable (fun y => k r y*v y) μ := by
    apply hE.mono' ((continuous_of_smoothFn (hk r (Ioo_subset_Icc_self hr))).aestronglyMeasurable.mul
      (continuous_of_smoothFn hv).aestronglyMeasurable)
    apply ae_of_all μ
    intro y
    change |k r y*v y| ≤ E y
    rw [mul_comm]
    exact (hEnvelope r (Ioo_subset_Icc_self hr) s hs y).1
  have hConv := exhaustionCutoff_integral_tendsto X o u hu hC
    (fun y => (hControl y).2.1) hCA hA0 μ (fun y => k r y*v y) hInt
  convert hConv using 1
  funext j
  apply integral_congr_ae
  exact ae_of_all μ (fun y => by
    change k r y*(exhaustionCutoff u A ((j:ℝ)+1) y*v y)=
      exhaustionCutoff u A ((j:ℝ)+1) y*(k r y*v y)
    ring)

end Yau.Proofs.F03Aux
