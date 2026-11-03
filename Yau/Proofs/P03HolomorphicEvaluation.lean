import Yau.Proofs.P03HolomorphicFunctionSpace

open scoped Manifold Topology

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

def holomorphicFunctionOf (f : M.Carrier → ℂ) (hf : IsHolomorphicFn f) :
    holomorphicFunctions M := ⟨⟨f, hf.continuous⟩, hf⟩

def holomorphicEvaluationCLM (x : M.Carrier) : holomorphicFunctions M →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM (R := ℂ) x).comp (holomorphicFunctions M).subtypeL

@[simp]
theorem holomorphicEvaluationCLM_apply (x : M.Carrier) (f : holomorphicFunctions M) :
    holomorphicEvaluationCLM x f = f.1 x := rfl

theorem holomorphicEvaluation_continuous :
    Continuous (fun p : holomorphicFunctions M × M.Carrier => p.1.1 p.2) := by
  letI := manifold_locallyCompact M
  exact continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)

theorem holomorphicTuple_completelyMetrizable (m : ℕ) :
    TopologicalSpace.IsCompletelyMetrizableSpace (Fin m → holomorphicFunctions M) := by
  letI := holomorphicFunctions_completelyMetrizable M
  infer_instance

theorem holomorphicTuple_baire (m : ℕ) : BaireSpace (Fin m → holomorphicFunctions M) := by
  letI := holomorphicFunctions_completelyMetrizable M
  infer_instance

theorem holomorphicTuple_nonempty (m : ℕ) : Nonempty (Fin m → holomorphicFunctions M) :=
  ⟨0⟩

end Yau.NodeProofs.P03Aux
