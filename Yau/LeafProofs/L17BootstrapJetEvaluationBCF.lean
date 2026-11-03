import Yau.LeafProofs.L17BootstrapJetEvaluationMap
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapJetEvaluationAux
open L17BootstrapClosedSlabAux

variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] {ι : Type} [TopologicalSpace ι]

def jetEvaluate (L : X →L[ℝ] BoundedContinuousFunction ι ℝ) (k : ℕ)
    (t : ι) (A : Jet E X k) : Jet E ℝ k :=
  jetMap (E := E) ((BoundedContinuousFunction.evalCLM ℝ t).comp L) k A

@[simp] theorem jetEvaluate_zero (L : X →L[ℝ] BoundedContinuousFunction ι ℝ) (t : ι) (A : X) :
    jetEvaluate (E := E) L 0 t A=L A t := rfl

@[simp] theorem jetEvaluate_succ (L : X →L[ℝ] BoundedContinuousFunction ι ℝ)
    (k : ℕ) (t : ι) (A : Jet E X (k+1)) (a : E) :
    jetAsCLM (jetEvaluate (E := E) L (k+1) t A) a=
      jetEvaluate (E := E) L k t (jetAsCLM A a) := rfl

theorem jetEvaluate_continuous [FiniteDimensional ℝ E]
    (L : X →L[ℝ] BoundedContinuousFunction ι ℝ) (k : ℕ) :
    Continuous (fun p : ι × Jet E X k => jetEvaluate (E := E) L k p.1 p.2) := by
  induction k with
  | zero =>
      change Continuous (fun p : ι × X => (L p.2) p.1)
      have hp : Continuous (fun p : ι × X => (L p.2,p.1)) :=
        (L.continuous.comp continuous_snd).prodMk continuous_fst
      exact continuous_eval.comp hp
  | succ k ih =>
      change Continuous (fun p : ι × (E →L[ℝ] Jet E X k) =>
        (jetMap (E := E) ((BoundedContinuousFunction.evalCLM ℝ p.1).comp L) k).comp p.2)
      apply continuous_clm_apply.mpr
      intro a
      have hp : Continuous (fun p : ι × (E →L[ℝ] Jet E X k) => (p.1,p.2 a)) :=
        continuous_fst.prodMk (continuous_snd.clm_apply continuous_const)
      exact ih.comp hp

def parameterJet (V : E → X) : (k : ℕ) → E → Jet E X k
  | 0 => V
  | k+1 => fderiv ℝ (parameterJet V k)

theorem parameterJet_contDiffOn {O : Set E} (hO : IsOpen O) {V : E → X}
    (hV : ContDiffOn ℝ ∞ V O) (k : ℕ) : ContDiffOn ℝ ∞ (parameterJet V k) O := by
  induction k with
  | zero => exact hV
  | succ k ih => exact ih.fderiv_of_isOpen hO (by simp)

theorem parameterJet_hasFDerivAt {O : Set E} (hO : IsOpen O) {V : E → X}
    (hV : ContDiffOn ℝ ∞ V O) (k : ℕ) {z : E} (hz : z∈O) :
    HasFDerivAt (parameterJet V k) (parameterJet V (k+1) z) z :=
  (((parameterJet_contDiffOn hO hV k).differentiableOn (by simp)).differentiableAt
    (hO.mem_nhds hz)).hasFDerivAt

end Yau.LeafProofs.L17BootstrapJetEvaluationAux
