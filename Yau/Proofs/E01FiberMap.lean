import Yau.Proofs.E01Congruence
import Mathlib.Topology.Semicontinuity.Basic

/-! Continuity and exact homogeneity under the fiber change used for John normalization. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem continuous_matrixFiberMap (S : Herm n) : Continuous (matrixFiberMap S) := by
  unfold matrixFiberMap Matrix.mulVec dotProduct
  fun_prop

theorem matrixFiberMap_complex_smul (S : Herm n) (c : ℂ) (η : ComplexVector n) :
    matrixFiberMap S (c • η) = c • matrixFiberMap S η := by
  apply WithLp.ofLp_injective
  change S *ᵥ (c • WithLp.ofLp η) = c • (S *ᵥ WithLp.ofLp η)
  exact Matrix.mulVec_smul _ _ _

theorem lowerSemicontinuous_comp_matrixFiberMap
    (v : ComplexVector n → EReal) (hv : LowerSemicontinuous v) (S : Herm n) :
    LowerSemicontinuous (fun η => v (matrixFiberMap S η)) :=
  hv.comp (continuous_matrixFiberMap S)

end Yau.NodeProofs.E01Aux
