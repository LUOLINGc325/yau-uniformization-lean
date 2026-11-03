import Yau.Proofs.P03SectionEvaluation
import Yau.Proofs.P03SpanContinuity
import Yau.Proofs.P03CompactGoodSets
import Yau.Proofs.P03FiniteAffinePerturbations

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}

def sectionCoordinateEvaluationCLM (a : ι → M.Carrier) (r : ι → ℝ) (i : ι)
    (z : chartClosedBall (a i) (r i)) : closedSectionArrays a r →L[ℂ] ComplexVector n :=
  (ContinuousMap.evalCLM (R := ℂ) z).comp
    ((ContinuousLinearMap.proj i).comp (closedSectionArrays a r).subtypeL)

@[simp]
theorem sectionCoordinateEvaluationCLM_apply (a : ι → M.Carrier) (r : ι → ℝ) (i : ι)
    (z : chartClosedBall (a i) (r i)) (b : closedSectionArrays a r) :
    sectionCoordinateEvaluationCLM a r i z b = b.1 i z := rfl

def fieldGoodSet (a : ι → M.Carrier) (r : ι → ℝ) (m : ℕ) (i : ι) :
    Set (Fin m → closedSectionArrays a r) :=
  {b | ∀ z : chartClosedBall (a i) (r i),
    Submodule.span ℂ (range fun j => (b j).1 i z) = ⊤}

theorem fieldGoodSet_isOpen (a : ι → M.Carrier) (r : ι → ℝ) (m : ℕ) (i : ι) :
    IsOpen (fieldGoodSet a r m i) := by
  have hv (j : Fin m) : Continuous
      (fun p : (Fin m → closedSectionArrays a r) × chartClosedBall (a i) (r i) =>
        (p.1 j).1 i p.2) := by
    have hb : Continuous
        (fun p : (Fin m → closedSectionArrays a r) × chartClosedBall (a i) (r i) =>
          (p.1 j).1 i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp
        ((continuous_apply j).comp continuous_fst))
    exact continuous_eval.comp (hb.prodMk continuous_snd)
  have hc := annihilatorEvaluationCLM_continuous
    (fun p : (Fin m → closedSectionArrays a r) × chartClosedBall (a i) (r i) =>
      fun j => (p.1 j).1 i p.2) hv
  have ho := isOpen_compact_injective _ hc
  convert ho using 1
  ext b
  apply forall_congr'
  intro z
  exact span_top_iff_annihilatorEvaluation_injective (fun j => (b j).1 i z)

theorem sectionCoordinates_finiteAffinePerturbation (a : ι → M.Carrier) (r : ι → ℝ)
    {m L : ℕ} (base : Fin m → closedSectionArrays a r) (W : Fin L → closedSectionArrays a r)
    (T : Fin m → Fin L → ℂ) (i : ι) (z : chartClosedBall (a i) (r i)) (j : Fin m) :
    (finiteAffinePerturbation base W T j).1 i z =
      (base j).1 i z + ∑ l, T j l • (W l).1 i z :=
  finiteAffinePerturbation_linearMap (sectionCoordinateEvaluationCLM a r i z).toLinearMap
    base W T j

end Yau.NodeProofs.P03Aux
