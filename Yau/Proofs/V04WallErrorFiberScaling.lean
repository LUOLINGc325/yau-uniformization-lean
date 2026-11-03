import Yau.Proofs.V04WallErrorFiberModel
import Yau.Proofs.V04WallErrorDilation
import Yau.Proofs.V04DataTransport

/-! The original radius update pulls back to a fixed fiber profile.
No new radius occurs in the compact coefficients. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n q : ℕ} {X : KahlerManifold n}

def fiberBaseWallModel (d : VariationData X q) (j : ℕ) (x : Pt X)
    (z : CotangentCoord n) : ℝ := wallBase d j (cotangentChartInv x z).1

def normalizedFiberWall (d : VariationData X q) (x : Pt X) (z : CotangentCoord n) : ℝ :=
  (normalizedFiberProfile d x z)⁻¹ - 1

theorem fiberNormModel_dilation (d : VariationData X q) (x : Pt X) (t b : ℝ)
    (z : CotangentCoord n) :
    fiberNormModel d x t (fiberDilation b z) = b ^ 2 * fiberNormModel d x t z := by
  have he := dualNorm_fiberScale_real (d.h t) b (cotangentChartInv x z)
  rw [fiberScale_chartInv] at he
  exact he

theorem deltaFiber_update_dilation (d : VariationData X q) (j : ℕ) (x : Pt X)
    {b : ℝ} (hb : b ≠ 0) (z : CotangentCoord n) :
    deltaFiber {d with B := Function.update d.B j b} j
      (cotangentChartInv x (fiberDilation b z)) = normalizedFiberProfile d x z := by
  simp only [deltaFiber, Function.update_self]
  change d.profileFiber (fiberNormModel d x 0 (fiberDilation b z) / b ^ 2) = _
  rw [fiberNormModel_dilation]
  have hquot : b ^ 2 * fiberNormModel d x 0 z / b ^ 2 = fiberNormModel d x 0 z := by
    field_simp
  rw [hquot]
  rfl

theorem boundaryCost_update_dilation (d : VariationData X q) (j : ℕ) (x : Pt X)
    {b : ℝ} (hb : b ≠ 0) (t s : ℝ) :
    (fun z => dualNorm (d.h t) (cotangentChartInv x (fiberDilation b z)).1
      (cotangentChartInv x (fiberDilation b z)).2 +
      wallCost {d with B := Function.update d.B j b} j
        (cotangentChartInv x (fiberDilation b z)) t s) =
    (fun z => b ^ 2 * fiberNormModel d x t z + fiberBaseModel d j x t z +
      (1 + s) * fiberBaseWallModel d j x z + (1 + s) * normalizedFiberWall d x z) := by
  funext z
  change fiberNormModel d x t (fiberDilation b z) +
    (fiberBaseModel d j x t z + (1 + s) *
      (fiberBaseWallModel d j x z +
        ((deltaFiber {d with B := Function.update d.B j b} j
          (cotangentChartInv x (fiberDilation b z)))⁻¹ - 1))) = _
  rw [fiberNormModel_dilation, deltaFiber_update_dilation d j x hb z]
  unfold normalizedFiberWall
  ring

theorem normBaseCost_dilation (d : VariationData X q) (j : ℕ) (x : Pt X)
    (b t s : ℝ) :
    (fun z => dualNorm (d.h t) (cotangentChartInv x (fiberDilation b z)).1
      (cotangentChartInv x (fiberDilation b z)).2 +
      (baseCost d j (cotangentChartInv x (fiberDilation b z)).1 t +
        (1 + s) * wallBase d j (cotangentChartInv x (fiberDilation b z)).1)) =
    (fun z => b ^ 2 * fiberNormModel d x t z + fiberBaseModel d j x t z +
      (1 + s) * fiberBaseWallModel d j x z) := by
  funext z
  change fiberNormModel d x t (fiberDilation b z) +
    (fiberBaseModel d j x t z + (1 + s) * fiberBaseWallModel d j x z) = _
  rw [fiberNormModel_dilation]
  ring

end Yau.Blueprint.V04Proof.WallErrorAux
