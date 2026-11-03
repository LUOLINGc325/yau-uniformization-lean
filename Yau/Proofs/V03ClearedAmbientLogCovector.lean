import Yau.Proofs.V03CovectorTransport
import Yau.Proofs.V03ActualLogMixedJet
import Yau.Proofs.V03AmbientTensorRegularity
import Yau.Proofs.V03TransitionInverse

/-! The genuine scaled logarithmic differential descends to a smooth
ambient covector at every cotangent point, including the wall zero set. -/

open scoped Topology ContDiff Matrix Manifold ComplexOrder

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def clearedLogChartCovector (d : VariationData X q) (j a : ℕ) (x : Pt X)
    (z : CotangentCoord n) : CotangentIndex n → ℂ :=
  clearedLogCovector (fun w => wallProduct d j (cotangentChartInv x w)) a cotangentDir z

def fixedAmbientLogCovector (d : VariationData X q) (j a : ℕ) (x : Pt X)
    (z : CotangentCoord n) : Fin q → ℂ :=
  ambientCovector (cotangentDG d.G x (cotangentChartInv x z)) (clearedLogChartCovector d j a x z)

theorem fixedAmbientLogCovector_entry_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (x : Pt X) (b : Fin q) :
    ContDiffOn ℝ ∞ (fun z => fixedAmbientLogCovector d j a x z b) (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hJ := gramLeftInverse_entry_contDiffOn
    (fun k i => (cotangentDG_chart_entry_contDiffOn hd.2.2.2.2.1.1 x k i).restrict_scalars ℝ)
    (fun z hz => ne_of_gt (cotangentDG_gram_posDef_in_chart hd.2.2.2.2.1 x _
      (cotangentChartInv_mapsTo x hz)).det_pos)
  change ContDiffOn ℝ ∞ (fun z => ∑ i, clearedLogChartCovector d j a x z i *
    gramLeftInverse (cotangentDG d.G x (cotangentChartInv x z)) i b) (cotangentTarget x)
  exact ContDiffOn.sum (fun i _ =>
    (clearedLogCovector_entry_contDiffOn hopen (wallProduct_chart_contDiffOn hd j x) a cotangentDir i).mul
      (hJ i b))

def ambientLogCovector (d : VariationData X q) (j a : ℕ)
    (y : CotangentPoint X.manifold) : Fin q → ℂ :=
  fixedAmbientLogCovector d j a y.1 (cotangentChart y.1 y)

theorem fixedAmbientLogCovector_eq_ambient {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) (x : Pt X)
    {y : CotangentPoint X.manifold} (hy : y ∈ cotangentSource x) :
    fixedAmbientLogCovector d j a x (cotangentChart x y) = ambientLogCovector d j a y := by
  have hself : y ∈ cotangentSource y.1 := mem_extChartAt_source _
  have hround := cotangentChart_left_inv x hy
  have hround0 := cotangentChart_left_inv y.1 hself
  have hz := cotangentChart_mapsTo x hy
  have hz0 := cotangentChart_mapsTo y.1 hself
  by_cases hp : wallProduct d j y = 0
  · have h1 := clearedLogCovector_zero
      (f := fun w => wallProduct d j (cotangentChartInv x w)) (z := cotangentChart x y)
      (by simpa only [hround] using hp) a (by omega : 2 ≤ a) cotangentDir
    have h2 := clearedLogCovector_zero
      (f := fun w => wallProduct d j (cotangentChartInv y.1 w)) (z := cotangentChart y.1 y)
      (by simpa only [hround0] using hp) a (by omega : 2 ≤ a) cotangentDir
    unfold ambientLogCovector fixedAmbientLogCovector clearedLogChartCovector
    rw [h1, h2]
    simp only [ambientCovector, Matrix.zero_vecMul]
  have hopen (x' : Pt X) : IsOpen (cotangentTarget x') :=
    (isOpen_extChartAt_target (I := ComplexModel n) x').prod isOpen_univ
  have hp₁ : wallProduct d j (cotangentChartInv x (cotangentChart x y)) ≠ 0 := by
    simpa only [hround] using hp
  have hp₂ : wallProduct d j (cotangentChartInv y.1 (cotangentChart y.1 y)) ≠ 0 := by
    simpa only [hround0] using hp
  have h1 := clearedLogCovector_eq
    (((wallProduct_chart_contDiffOn hd j x).contDiffAt ((hopen x).mem_nhds hz)).differentiableAt (by simp))
    hp₁ a (by omega : 1 ≤ a) cotangentDir
  have h2 := clearedLogCovector_eq
    (((wallProduct_chart_contDiffOn hd j y.1).contDiffAt ((hopen y.1).mem_nhds hz0)).differentiableAt (by simp))
    hp₂ a (by omega : 1 ≤ a) cotangentDir
  have hW := scalarWirt_in_fixed_chart (fun u => Real.log (wallProduct d j u)) x hy
    ((logWall_chart_contDiffAt hd j x hy hp).differentiableAt (by norm_num))
  have hT : IsUnit (cotangentTransition y.1 x y) :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (cotangentTransition_mulVec_injective y.1 x y hself hy)
  unfold ambientLogCovector fixedAmbientLogCovector clearedLogChartCovector
  rw [h1, h2, hround, hround0, hW,
    cotangentDG_transition hd.2.2.2.2.1.1 y.1 x y hself hy, ← Matrix.smul_vecMul]
  exact (ambientCovector_covariant (cotangentDG d.G x y)
    ((wallProduct d j y : ℂ) ^ a • (fun i => wirt
      (fun z => (Real.log (wallProduct d j (cotangentChartInv x z)) : ℂ))
      (cotangentChart x y) (cotangentDir i))) (cotangentTransition y.1 x y) hT).symm

theorem ambientLogCovector_chart_entry_contDiffOn {d : VariationData X q}
    (hd : VariationSetup d) (j a : ℕ) (ha : 4 ≤ a) (x : Pt X) (b : Fin q) :
    ContDiffOn ℝ ∞ (fun z => ambientLogCovector d j a (cotangentChartInv x z) b)
      (cotangentTarget x) := by
  apply (fixedAmbientLogCovector_entry_contDiffOn hd j a x b).congr
  intro z hz
  have hh := congrFun
    (fixedAmbientLogCovector_eq_ambient hd j a ha x (cotangentChartInv_mapsTo x hz)) b
  rw [cotangentChart_right_inv x hz] at hh
  exact hh.symm

end Yau.Blueprint.V03Proof
