import Yau.Proofs.V03WallHessian

/-! A native chart representative for the actual scaled reciprocal-wall
Hessian. It is smooth across the cutoff boundary for every allowed exponent. -/

open scoped Topology ContDiff Matrix Manifold

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def clearedWallTensor (d : VariationData X q) (j a : ℕ) (x : Pt X)
    (z : CotangentCoord n) : CotangentMatrix n :=
  clearedWallHessian (fun w => deltaBase d j (cotangentChartInv x w).1)
    (fun w => deltaFiber d j (cotangentChartInv x w)) (2 * a) cotangentDir z

theorem clearedWallTensor_entry_contDiffOn {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (x : Pt X) (r s : CotangentIndex n) :
    ContDiffOn ℝ ∞ (fun z => clearedWallTensor d j a x z r s) (cotangentTarget x) := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact clearedWallHessian_entry_contDiffOn hopen (deltaBase_chart_contDiffOn hd j x)
    (deltaFiber_chart_contDiffOn hd j x) (2 * a) cotangentDir r s

theorem clearedWallTensor_eq {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    (hb : deltaBase d j (cotangentChartInv x z).1 ≠ 0)
    (hf : deltaFiber d j (cotangentChartInv x z) ≠ 0) :
    clearedWallTensor d j a x z =
      ((wallPower d j a (cotangentChartInv x z)) ^ 2 : ℂ) •
        leviMatrix (fun w => wallBase d j (cotangentChartInv x w).1 +
          wallFiber d j (cotangentChartInv x w)) z cotangentDir := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  have hbC : ContDiffAt ℝ 2 (fun w => deltaBase d j (cotangentChartInv x w).1) z :=
    ((deltaBase_chart_contDiffOn hd j x).contDiffAt (hopen.mem_nhds hz)).of_le (by simp)
  have hfC : ContDiffAt ℝ 2 (fun w => deltaFiber d j (cotangentChartInv x w)) z :=
    ((deltaFiber_chart_contDiffOn hd j x).contDiffAt (hopen.mem_nhds hz)).of_le (by simp)
  have heq := clearedWallHessian_eq hbC hfC hb hf cotangentDir (m := 2 * a) (by omega)
  have hpow : ((deltaBase d j (cotangentChartInv x z).1 *
      deltaFiber d j (cotangentChartInv x z)) ^ (2 * a) : ℝ) =
      (wallPower d j a (cotangentChartInv x z)) ^ 2 := by
    unfold wallPower wallProduct
    rw [← pow_mul]
    congr 1
    omega
  simpa only [clearedWallTensor, wallBase, wallFiber, hpow, Complex.ofReal_pow] using heq

theorem clearedWallTensor_isHermitian {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x) :
    (clearedWallTensor d j a x z).IsHermitian := by
  have hopen : IsOpen (cotangentTarget x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_univ
  exact clearedWallHessian_isHermitian
    (((deltaBase_chart_contDiffOn hd j x).contDiffAt (hopen.mem_nhds hz)).of_le (by simp))
    (((deltaFiber_chart_contDiffOn hd j x).contDiffAt (hopen.mem_nhds hz)).of_le (by simp))
    cotangentDir (by omega : 4 ≤ 2 * a)

end Yau.Blueprint.V03Proof
