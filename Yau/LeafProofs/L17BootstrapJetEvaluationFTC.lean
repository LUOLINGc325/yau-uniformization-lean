import Yau.LeafProofs.L17BootstrapJetEvaluationBCF
import Yau.LeafProofs.L17SchauderSpaceFTC
import Mathlib.Topology.Order.ProjIcc

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapJetEvaluationAux
open L17BootstrapClosedSlabAux

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  {T : ℝ} (hT : 0<T)
  (LV LB : X →L[ℝ] BoundedContinuousFunction (↥(Icc (0:ℝ) T)) ℝ)
  (hFTC : ∀ u : X, ∀ s t : ↥(Icc (0:ℝ) T), LV u t-LV u s=
    ∫ tau in (s:ℝ)..(t:ℝ), LB u (projIcc 0 T hT.le tau))

theorem jetEvaluate_time_continuous (k : ℕ) (A : Jet E X k) :
    Continuous (fun tau : ℝ => jetEvaluate (E := E) LB k (projIcc 0 T hT.le tau) A) :=
by
  have hp : Continuous (fun tau : ℝ => (projIcc 0 T hT.le tau,A)) :=
    (continuous_projIcc : Continuous (projIcc (0:ℝ) T hT.le)).prodMk continuous_const
  exact (jetEvaluate_continuous LB k).comp hp

include hFTC

theorem jetEvaluate_timeFTC (k : ℕ) : ∀ (A : Jet E X k) (s t : ↥(Icc (0:ℝ) T)),
    jetEvaluate (E := E) LV k t A-jetEvaluate LV k s A=
      ∫ tau in (s:ℝ)..(t:ℝ), jetEvaluate LB k (projIcc 0 T hT.le tau) A := by
  induction k with
  | zero => exact hFTC
  | succ k ih =>
      intro A s t
      change jetAsCLM (jetEvaluate (E := E) LV (k+1) t A)-
          jetAsCLM (jetEvaluate LV (k+1) s A)=
          ∫ tau in (s:ℝ)..(t:ℝ), jetAsCLM (jetEvaluate LB (k+1) (projIcc 0 T hT.le tau) A)
      apply ContinuousLinearMap.ext
      intro a
      have hc : Continuous (fun tau : ℝ =>
          jetAsCLM (jetEvaluate (E := E) LB (k+1) (projIcc 0 T hT.le tau) A)) := by
        change Continuous (fun tau : ℝ => jetEvaluate (E := E) LB (k+1) (projIcc 0 T hT.le tau) A)
        exact jetEvaluate_time_continuous (E := E) hT LB (k+1) A
      have hInt : IntervalIntegrable (fun tau =>
          jetAsCLM (jetEvaluate (E := E) LB (k+1) (projIcc 0 T hT.le tau) A)) volume (s:ℝ) t :=
        hc.intervalIntegrable (s:ℝ) t
      calc
        _ = ∫ tau in (s:ℝ)..(t:ℝ), jetEvaluate LB k (projIcc 0 T hT.le tau) (jetAsCLM A a) :=
          ih (jetAsCLM A a) s t
        _ = _ := (ContinuousLinearMap.intervalIntegral_apply hInt a).symm

theorem jetEvaluate_time_hasDerivWithinAt (k : ℕ) (A : Jet E X k)
    (t : ↥(Icc (0:ℝ) T)) :
    HasDerivWithinAt
      (fun tau => jetEvaluate (E := E) LV k (projIcc 0 T hT.le tau) A)
      (jetEvaluate LB k t A) (Icc 0 T) (t:ℝ) := by
  have h := L17SchauderAux.hasDerivWithinAt_of_interval_integral hT.le
    (jetEvaluate_time_continuous (E := E) hT LB k A) (f := fun tau =>
      jetEvaluate LV k (projIcc 0 T hT.le tau) A) ?_ t.property
  · simpa only [projIcc_val] using h
  · intro s hs r hr
    simpa only [projIcc_of_mem hT.le hs,projIcc_of_mem hT.le hr] using
      jetEvaluate_timeFTC (E := E) hT LV LB hFTC k A ⟨s,hs⟩ ⟨r,hr⟩


end Yau.LeafProofs.L17BootstrapJetEvaluationAux
