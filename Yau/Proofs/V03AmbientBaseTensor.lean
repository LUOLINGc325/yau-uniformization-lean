import Yau.Proofs.V03BaseCotangentMatrixTransport
import Yau.Proofs.V03AmbientTensorRegularity
import Yau.Proofs.V03TransitionInverse

/-! The actual original base metric descends through the immersion Gram
left inverse to one smooth intrinsic ambient Hermitian tensor. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

def fixedAmbientBaseTensor (G : CotangentPoint M → ComplexVector q)
    (h : HermitianField M) (x : M.Carrier) (z : CotangentCoord n) : Matrix (Fin q) (Fin q) ℂ :=
  ambientLeviTensor (cotangentDG G x (cotangentChartInv x z)) (baseCotangentMatrix h x z)

def ambientBaseTensor (G : CotangentPoint M → ComplexVector q)
    (h : HermitianField M) (y : CotangentPoint M) : Matrix (Fin q) (Fin q) ℂ :=
  fixedAmbientBaseTensor G h y.1 (cotangentChart y.1 y)

theorem fixedAmbientBaseTensor_entry_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (g : SmoothMetric M) (x : M.Carrier) (a b : Fin q) :
    ContDiffOn ℝ ∞ (fun z => fixedAmbientBaseTensor G g.form x z a b) (cotangentTarget x) := by
  exact ambientLeviTensor_entry_contDiffOn
    (fun k i => (cotangentDG_chart_entry_contDiffOn hG.1 x k i).restrict_scalars ℝ)
    (baseCotangentMatrix_entry_contDiffOn g x)
    (fun z hz => ne_of_gt (cotangentDG_gram_posDef_in_chart hG x _
      (cotangentChartInv_mapsTo x hz)).det_pos) a b

theorem fixedAmbientBaseTensor_eq_ambient {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (h : HermitianField M) (x : M.Carrier) {y : CotangentPoint M}
    (hy : y ∈ cotangentSource x) :
    fixedAmbientBaseTensor G h x (cotangentChart x y) = ambientBaseTensor G h y := by
  have hs : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hT : IsUnit (cotangentTransition y.1 x y) :=
    Matrix.mulVec_injective_iff_isUnit.mp (cotangentTransition_mulVec_injective y.1 x y hs hy)
  unfold ambientBaseTensor fixedAmbientBaseTensor
  rw [cotangentChart_left_inv x hy, cotangentChart_left_inv y.1 hs,
    baseCotangentMatrix_chart_change h y.1 x hs hy,
    cotangentDG_transition hG.1 y.1 x y hs hy]
  exact (ambientLeviTensor_covariant _ _ _ hT).symm

theorem ambientBaseTensor_chart_entry_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (g : SmoothMetric M) (x : M.Carrier) (a b : Fin q) :
    ContDiffOn ℝ ∞ (fun z => ambientBaseTensor G g.form (cotangentChartInv x z) a b)
      (cotangentTarget x) := by
  apply (fixedAmbientBaseTensor_entry_contDiffOn hG g x a b).congr
  intro z hz
  have hh := congrArg (fun H : Matrix (Fin q) (Fin q) ℂ => H a b)
    (fixedAmbientBaseTensor_eq_ambient hG g.form x (cotangentChartInv_mapsTo x hz))
  rw [cotangentChart_right_inv x hz] at hh
  exact hh.symm

end Yau.Blueprint.V03Proof
