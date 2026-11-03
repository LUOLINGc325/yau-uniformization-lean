import Yau.Proofs.F03MetricDefectForm
import Yau.Proofs.F03HodgeZero
import Yau.Proofs.F03LeviNegative
import Yau.Proofs.F03BoundedInitialFaceProducer
import Yau.Proofs.P06Geometry

/-! The actual scalar heat integral has the exact closed-potential identity from the registered P06 ancestor. -/
noncomputable section
open MeasureTheory Set
open scoped ComplexOrder Interval
namespace Yau.Proofs.F03Aux
open Yau Blueprint HeatConcreteBindings HeatTargetCandidates
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def metricDefectHeatCorrection
    (X : KahlerManifold n) (h : Flow X)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O)
    (L : ℝ) (x : Pt X) (s : ℝ) : ℝ :=
  -(∫ b in (0:ℝ)..L^2,boundedKernelEvolution μ
    (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO) (flowMetricDefect X h s) b x)

theorem flowMetricDefect_hodge_heat_correction (hP06 : P06)
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) {s : ℝ} (hs : 0 ≤ s) :
    ∃ V : ℝ → RealForm X.manifold 2,
      IsBoundedFormHeat X.metric.form (flowMetricDefectForm X h s) V ∧
      (∀ b,0 < b → ∀ x,(formHermitianMatrix (V b) x).PosSemidef) ∧
      ∀ (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
        (O : ℕ → Set (Pt X)) (hO : SmoothExhaustion O),
      (∀ b,0 < b → ∀ x,formTrace X.metric.form (V b) x=
        boundedKernelEvolution μ (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
          (flowMetricDefect X h s) b x) ∧
      ∀ L : ℝ,0 < L →
      (∀ x,IntervalIntegrable (fun b => boundedKernelEvolution μ
        (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
        (flowMetricDefect X h s) b x) volume 0 (L^2)) ∧
      ∀ x,levi (fun y => metricDefectHeatCorrection X h μ hμ O hO L y s) x=
        gMat X.metric.form x-gMat (h s) x-formHermitianMatrix (V (L^2)) x := by
  rcases (hP06 n X).1 (NodeProofs.P06Aux.nonnegativeHBC X) with
    ⟨_hCalc,_hNorm,_hRepresentation,_hTraceData,hExist,_hScalar,hOrder,hTrace,_hSemigroup,hClosed,_hRemaining⟩
  have hData := flowMetricDefectForm_data X o h U P ρ hf hs
  obtain ⟨V,hV⟩ := (hExist (flowMetricDefectForm X h s) hData.1).1
  refine ⟨V,hV,fun b hb => hodgeHeat_nonnegative_of_registered_order X.metric.form hOrder
    _ V hData.1 hV hData.2.2 hb,fun μ hμ O hO => ?_⟩
  have hScalar : IsBoundedScalarHeat X.metric.form (formTrace X.metric.form (flowMetricDefectForm X h s))
      (boundedKernelEvolution μ (dirichletMinimalKernelCandidate X.metric X.kahler_metric μ hμ O hO)
        (flowMetricDefect X h s)) := by
    rw [flowMetricDefectForm_trace]
    exact dirichletMinimalBoundedHeat_class X.metric X.kahler_metric μ hμ O hO (flowMetricDefect X h s)
      (flowMetricDefect_smooth X o h U P ρ hf hs) ⟨n,flowMetricDefect_abs_bound X o h U P ρ hf hs⟩
  refine ⟨hTrace _ V _ hData.1 hV hScalar,fun L hL => ?_⟩
  have hPotential := hClosed _ V _ hData.1 hData.2.1 hV hScalar (L^2) (sq_pos_of_pos hL)
  refine ⟨hPotential.2.1,fun x => ?_⟩
  dsimp only [metricDefectHeatCorrection]
  rw [levi_negative,hPotential.2.2 x,flowMetricDefectForm_matrix]
  abel

end Yau.Proofs.F03Aux
