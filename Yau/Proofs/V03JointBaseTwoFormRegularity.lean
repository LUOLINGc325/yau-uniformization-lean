import Yau.Proofs.V03JointBaseTwoForm
import Yau.Proofs.V03FixedBaseTwoFormSmooth
import Yau.Proofs.V03ChartKahlerClosed

/-! The intrinsic actual base area form is smooth on the original
parameter set and closed at interior points by the original Kähler condition. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]

theorem jointBaseTwoForm_contDiffOn (g : SmoothMetric M)
    {f : P → CotangentPoint M} {S : Set P}
    (hf : CotangentHolomorphicOn f S) (hS : UniqueDiffOn ℂ S) :
    ContDiffOn ℝ ∞ (jointBaseTwoForm g.form f S) S := by
  intro p hp
  obtain ⟨V, hV, hpV, hsource, hcoord⟩ := hf.2 p hp
  have hu : UniqueDiffOn ℂ (S ∩ V) := fun r hr => (hS r hr.1).inter (hV.mem_nhds hr.2)
  have hc : ContDiffOn ℂ ∞ (fun r => chartPt (f p).1 (f r).1) (S ∩ V) := hcoord.fst
  have hmodel := fixedBaseTwoForm_contDiffOn g (f p).1 hu hc
    (fun r hr => (extChartAt (ComplexModel n) (f p).1).map_source (hsource r hr))
  apply (contDiffWithinAt_inter (hV.mem_nhds hpV)).mp
  apply (hmodel p ⟨hp, hpV⟩).congr_of_eventuallyEq_of_mem ?_ ⟨hp, hpV⟩
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [jointBaseTwoForm_eq_fixed_chart g.form hf hr.1 (hS r hr.1) (f p).1 (hsource r hr),
    fderivWithin_inter (hV.mem_nhds hr.2)]

theorem jointBaseTwoForm_closed (g : SmoothMetric M) (hK : IsKahler g)
    {f : P → CotangentPoint M} {S : Set P}
    (hf : CotangentHolomorphicOn f S) (hS : UniqueDiffOn ℂ S)
    {p : P} (hp : p ∈ interior S) : extDeriv (jointBaseTwoForm g.form f S) p = 0 := by
  obtain ⟨V, hV, hpV, hsource, hcoord⟩ := hf.2 p (interior_subset hp)
  let W : Set P := interior S ∩ V
  have hW : IsOpen W := isOpen_interior.inter hV
  have hpW : p ∈ W := ⟨hp, hpV⟩
  have hsub : W ⊆ S ∩ V := fun r hr => ⟨interior_subset hr.1, hr.2⟩
  let c : P → ComplexVector n := fun r => chartPt (f p).1 (f r).1
  have hc : ContDiffOn ℂ ∞ c W := hcoord.fst.mono hsub
  have heq : jointBaseTwoForm g.form f S =ᶠ[𝓝 p]
      (fun r => (chartKahlerTwoForm g.form (f p).1 (c r)).compContinuousLinearMap (fderiv ℝ c r)) := by
    filter_upwards [hW.mem_nhds hpW] with r hr
    rw [jointBaseTwoForm_eq_fixed_chart g.form hf (hsub hr).1 (hS r (hsub hr).1)
      (f p).1 (hsource r (hsub hr))]
    have hSn : S ∈ 𝓝 r := mem_of_superset (isOpen_interior.mem_nhds hr.1) interior_subset
    rw [fderivWithin_of_mem_nhds hSn,
      ((hc.contDiffAt (hW.mem_nhds hr)).differentiableAt (by simp)).fderiv_restrictScalars ℝ]
  rw [heq.extDeriv_eq]
  have hΩ : DifferentiableAt ℝ (chartKahlerTwoForm g.form (f p).1) (c p) :=
    ((chartKahlerTwoForm_contDiffOn g (f p).1).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) (f p).1).mem_nhds
        (mem_extChartAt_target (f p).1))).differentiableAt (by simp)
  exact closedTwoForm_pullback hΩ
    ((hc.contDiffAt (hW.mem_nhds hpW)).restrict_scalars ℝ |>.of_le (by simp))
    (chartKahlerTwoForm_closed_center g hK (f p).1)

end Yau.Blueprint.V03Proof
