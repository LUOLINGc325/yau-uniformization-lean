import Yau.Proofs.V03ClearedLogMatrix
import Yau.Proofs.V03ActualLogMixedJet
import Yau.Proofs.V03SpatialHessianTransport
import Yau.Proofs.V03AmbientTensorRegularity
import Yau.Proofs.V03TransitionInverse

/-! The genuine scaled logarithmic Levi form descends to a smooth
ambient tensor, including every zero of the original wall product. -/

open scoped Topology ContDiff Matrix Manifold ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def clearedLogTensor (d : VariationData X q) (j a : ℕ) (x : Pt X)
    (z : CotangentCoord n) : CotangentMatrix n :=
  clearedLogMatrix (fun w => wallProduct d j (cotangentChartInv x w)) (2 * a) cotangentDir z

theorem clearedLogTensor_entry_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (x : Pt X) (b c : CotangentIndex n) :
    ContDiffOn ℝ ∞ (fun z => clearedLogTensor d j a x z b c) (cotangentTarget x) :=
  clearedLogMatrix_entry_contDiffOn
    ((isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ)
    (wallProduct_chart_contDiffOn hd j x) (2 * a) cotangentDir b c

def fixedAmbientLogTensor (d : VariationData X q) (j a : ℕ) (x : Pt X)
    (z : CotangentCoord n) : Matrix (Fin q) (Fin q) ℂ :=
  ambientLeviTensor (cotangentDG d.G x (cotangentChartInv x z)) (clearedLogTensor d j a x z)

theorem fixedAmbientLogTensor_entry_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (x : Pt X) (b c : Fin q) :
    ContDiffOn ℝ ∞ (fun z => fixedAmbientLogTensor d j a x z b c) (cotangentTarget x) := by
  apply ambientLeviTensor_entry_contDiffOn
    (fun k i => (cotangentDG_chart_entry_contDiffOn hd.2.2.2.2.1.1 x k i).restrict_scalars ℝ)
    (clearedLogTensor_entry_contDiffOn hd j a x) _ b c
  intro z hz
  exact ne_of_gt (cotangentDG_gram_posDef_in_chart hd.2.2.2.2.1 x _
    (cotangentChartInv_mapsTo x hz)).det_pos

def ambientLogTensor (d : VariationData X q) (j a : ℕ)
    (y : CotangentPoint X.manifold) : Matrix (Fin q) (Fin q) ℂ :=
  fixedAmbientLogTensor d j a y.1 (cotangentChart y.1 y)

theorem fixedAmbientLogTensor_eq_ambient {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) (x : Pt X)
    {y : CotangentPoint X.manifold} (hy : y ∈ cotangentSource x) :
    fixedAmbientLogTensor d j a x (cotangentChart x y) = ambientLogTensor d j a y := by
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hround := cotangentChart_left_inv x hy
  have hround0 := cotangentChart_left_inv y.1 hself
  have hz := cotangentChart_mapsTo x hy
  have hz0 := cotangentChart_mapsTo y.1 hself
  by_cases hp : wallProduct d j y = 0
  · have h1 := clearedLogMatrix_zero
      (f := fun w => wallProduct d j (cotangentChartInv x w))
      (z := cotangentChart x y)
      (by simpa only [hround] using hp) cotangentDir (by omega : 3 ≤ 2 * a)
    have h2 := clearedLogMatrix_zero
      (f := fun w => wallProduct d j (cotangentChartInv y.1 w))
      (z := cotangentChart y.1 y)
      (by simpa only [hround0] using hp) cotangentDir (by omega : 3 ≤ 2 * a)
    unfold ambientLogTensor fixedAmbientLogTensor clearedLogTensor
    rw [h1, h2]
    simp only [ambientLeviTensor, Matrix.mul_zero, Matrix.zero_mul]
  have hopen (x' : Pt X) : IsOpen (cotangentTarget x') :=
    (isOpen_extChartAt_target (I := ComplexModel n) x').prod isOpen_univ
  have hp₁ : wallProduct d j (cotangentChartInv x (cotangentChart x y)) ≠ 0 := by
    simpa only [hround] using hp
  have hp₂ : wallProduct d j (cotangentChartInv y.1 (cotangentChart y.1 y)) ≠ 0 := by
    simpa only [hround0] using hp
  have h1 := clearedLogMatrix_eq
    (((wallProduct_chart_contDiffOn hd j x).contDiffAt ((hopen x).mem_nhds hz)).of_le (by simp))
    hp₁ cotangentDir (by omega : 2 ≤ 2 * a)
  have h2 := clearedLogMatrix_eq
    (((wallProduct_chart_contDiffOn hd j y.1).contDiffAt ((hopen y.1).mem_nhds hz0)).of_le (by simp))
    hp₂ cotangentDir (by omega : 2 ≤ 2 * a)
  have hH := spatialHessian_in_fixed_chart (fun u => Real.log (wallProduct d j u)) x hy
    (logWall_chart_contDiffAt hd j x hy hp)
  have hT : IsUnit (cotangentTransition y.1 x y) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (cotangentTransition_mulVec_injective y.1 x y hself hy)
  unfold ambientLogTensor fixedAmbientLogTensor clearedLogTensor
  rw [h1, h2, hround, hround0]
  change _ = ambientLeviTensor (cotangentDG d.G y.1 y)
    ((wallProduct d j y : ℂ) ^ (2 * a) • spatialHessian (fun u => Real.log (wallProduct d j u)) y)
  rw [hH, cotangentDG_transition hd.2.2.2.2.1.1 y.1 x y hself hy]
  have hc := ambientLeviTensor_covariant (cotangentDG d.G x y)
    ((wallProduct d j y : ℂ) ^ (2 * a) •
      leviMatrix (fun w => Real.log (wallProduct d j (cotangentChartInv x w)))
        (cotangentChart x y) cotangentDir) (cotangentTransition y.1 x y) hT
  simpa only [Matrix.smul_mul, Matrix.mul_smul] using hc.symm

theorem ambientLogTensor_chart_entry_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) (x : Pt X) (b c : Fin q) :
    ContDiffOn ℝ ∞ (fun z => ambientLogTensor d j a (cotangentChartInv x z) b c)
      (cotangentTarget x) := by
  apply (fixedAmbientLogTensor_entry_contDiffOn hd j a x b c).congr
  intro z hz
  have hh := congrArg (fun A : Matrix (Fin q) (Fin q) ℂ => A b c)
    (fixedAmbientLogTensor_eq_ambient hd j a ha x (cotangentChartInv_mapsTo x hz))
  rw [cotangentChart_right_inv x hz] at hh
  exact hh.symm

end Yau.Blueprint.V03Proof
