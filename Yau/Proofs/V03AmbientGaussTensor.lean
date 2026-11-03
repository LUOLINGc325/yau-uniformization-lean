import Yau.Proofs.V03GaussLeviMatrixTransport
import Yau.Proofs.V03AmbientTensorRegularity

/-! The actual Gauss Levi form descends through the immersion Gram left
inverse to one globally defined smooth ambient Hermitian tensor. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {M : ComplexManifold n}

def fixedAmbientGaussTensor (G : CotangentPoint M → ComplexVector q) (x : M.Carrier)
    (z : CotangentCoord n) : Matrix (Fin q) (Fin q) ℂ :=
  ambientLeviTensor (cotangentDG G x (cotangentChartInv x z))
    (leviMatrix (gaussPotential G x) z cotangentDir)

def ambientGaussTensor (G : CotangentPoint M → ComplexVector q) (y : CotangentPoint M) :
    Matrix (Fin q) (Fin q) ℂ :=
  fixedAmbientGaussTensor G y.1 (cotangentChart y.1 y)

theorem fixedAmbientGaussTensor_entry_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (x : M.Carrier) (a b : Fin q) :
    ContDiffOn ℝ ∞ (fun z => fixedAmbientGaussTensor G x z a b) (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hpot : ContDiffOn ℝ ∞ (gaussPotential G x) (cotangentTarget x) :=
    fun z hz => (gaussPotential_contDiffAt hG x hz).contDiffWithinAt
  exact ambientLeviTensor_entry_contDiffOn
    (fun k i => (cotangentDG_chart_entry_contDiffOn hG.1 x k i).restrict_scalars ℝ)
    (leviMatrix_entry_contDiffOn hopen hpot cotangentDir)
    (fun z hz => ne_of_gt (cotangentDG_gram_posDef_in_chart hG x _
      (cotangentChartInv_mapsTo x hz)).det_pos) a b

theorem fixedAmbientGaussTensor_eq_ambient {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (x : M.Carrier) {y : CotangentPoint M}
    (hy : y ∈ cotangentSource x) :
    fixedAmbientGaussTensor G x (cotangentChart x y) = ambientGaussTensor G y := by
  have hs : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hT : IsUnit (cotangentTransition y.1 x y) :=
    Matrix.mulVec_injective_iff_isUnit.mp (cotangentTransition_mulVec_injective y.1 x y hs hy)
  unfold ambientGaussTensor fixedAmbientGaussTensor
  rw [cotangentChart_left_inv x hy, cotangentChart_left_inv y.1 hs,
    gaussLeviMatrix_chart_change hG y.1 x hs hy,
    cotangentDG_transition hG.1 y.1 x y hs hy]
  exact (ambientLeviTensor_covariant _ _ _ hT).symm

theorem ambientGaussTensor_chart_entry_contDiffOn {G : CotangentPoint M → ComplexVector q}
    (hG : CotangentImmersion G) (x : M.Carrier) (a b : Fin q) :
    ContDiffOn ℝ ∞ (fun z => ambientGaussTensor G (cotangentChartInv x z) a b)
      (cotangentTarget x) := by
  apply (fixedAmbientGaussTensor_entry_contDiffOn hG x a b).congr
  intro z hz
  have hh := congrArg (fun H : Matrix (Fin q) (Fin q) ℂ => H a b)
    (fixedAmbientGaussTensor_eq_ambient hG x (cotangentChartInv_mapsTo x hz))
  rw [cotangentChart_right_inv x hz] at hh
  exact hh.symm

end Yau.Blueprint.V03Proof
