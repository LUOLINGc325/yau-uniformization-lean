import Yau.Proofs.P03DerivativeEvaluation
import Yau.Proofs.P03CompactGoodSets

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n N : ℕ} {M : ComplexManifold n}

def immersionGoodSet (a : M.Carrier) (K : Set (ComplexVector n)) (N : ℕ) :
    Set (Fin N → holomorphicFunctions M) :=
  {f | ∀ z : K, Function.Injective (tupleDerivativeCLM a f z.1)}

theorem immersionGoodSet_isOpen (a : M.Carrier) (K : Set (ComplexVector n))
    (hK : IsCompact K) (hsub : K ⊆ chartTarget a) :
    IsOpen (immersionGoodSet a K N) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : (Fin N → holomorphicFunctions M) × K =>
      tupleDerivativeCLM a p.1 p.2.1) :=
    (continuousOn_tupleDerivativeCLM a).comp_continuous
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨mem_univ _, hsub p.2.2⟩)
  exact isOpen_compact_injective _ hc

end Yau.NodeProofs.P03Aux
