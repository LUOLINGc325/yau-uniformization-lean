import Yau.Proofs.P06TimeIntegralPotentialScalar
import Yau.Proofs.P06TimeIntegralPotentialEvolution

/-! The time-integral half of the original P06 closed-potential assertion.
Positive-time closedness is an explicit natural internal hypothesis; the
parent construction supplies it before assembling HodgeClosedPotential. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold Matrix
namespace Yau.NodeProofs.P06Aux.TimePotential
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem boundedFormHeat_timeIntegralPotential (X : KahlerManifold n)
    {A : RealForm X.manifold 2} {U : ℝ → RealForm X.manifold 2}
    {u : ℝ → X.manifold.Carrier → ℝ}
    (hA : BoundedOneOneData X.metric.form A)
    (hU : IsBoundedFormHeat X.metric.form A U)
    (hu : IsBoundedScalarHeat X.metric.form (formTrace X.metric.form A) u)
    (hclosed : ∀ s, 0 < s → ClosedRealForm (U s))
    {T : ℝ} (hT : 0 < T) :
    (∀ x, IntervalIntegrable (fun s => u s x) volume 0 T) ∧
      ∀ x, formHermitianMatrix (U T) x = formHermitianMatrix A x +
        levi (fun y => ∫ s in (0 : ℝ)..T, u s y) x := by
  have hf : SmoothFn (formTrace X.metric.form A) :=
    (hodgeGeometry X).2.2.2.1 A hA.1 hA.2.1
  have htrace : ∀ s, 0 < s → formTrace X.metric.form (U s) = u s := by
    intro s hs
    funext x
    exact PDETypeTrace.hodgeTraceCommutation X A U u hA hU hu s hs x
  have hderiv (s : ℝ) (hs : 0 < s) (x : X.manifold.Carrier) (a b : Fin n) :
      HasDerivAt (fun r => formHermitianMatrix (U r) x a b) (levi (u s) x a b) s := by
    simpa only [htrace s hs] using
      closed_formHeat_matrix_hasDerivAt X hA hU hs (hclosed s hs) x a b
  refine ⟨boundedScalarHeat_intervalIntegrable hu hT, ?_⟩
  intro x
  ext a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hT
    (fun s hs => hderiv s hs.1 x a b)
    (boundedScalarHeat_levi_intervalIntegrable hf hu hT x a b)
    (formHermitianMatrix_initial_tendsto hU.2.1 x a b)
    ((hderiv T hT x a b).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  change formHermitianMatrix (U T) x a b = formHermitianMatrix A x a b +
    levi (fun y => ∫ s in (0 : ℝ)..T, u s y) x a b
  rw [boundedScalarHeat_levi_integral hf hu hT x a b]
  rw [hFTC]
  abel

end Yau.NodeProofs.P06Aux.TimePotential
