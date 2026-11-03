import Yau.Proofs.V04WallErrorFiberLocal

/-! The base term in the evolution identity is locally smooth at every
point of the actual boundary region. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem baseCost_smoothSpaceTime {d : VariationData X q} (hd : VariationSetup d) (j : ℕ) :
    SmoothSpaceTime (baseCost d j) (Set.Icc 0 d.extendedT) := by
  intro x
  exact (contDiffOn_const.mul (hd.2.2.2.2.2.2.2.2.1.1 x)).add
    ((hd.2.2.2.2.2.2.2.2.2.1 j).1 x)

theorem baseCost_wall_inChart_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {t : ℝ} (ht : t ∈ Set.Icc 0 d.T) (s : ℝ)
    (hδ : deltaBase d j x ≠ 0) :
    ContDiffAt ℝ ∞
      ((fun w => baseCost d j w t + (1 + s) * wallBase d j w) ∘ chartInv x)
      (chartPt x x) := by
  have hOp := isOpen_extChartAt_target (I := ComplexModel n) x
  have hbase := spatial_slice_contDiffAt hOp ((baseCost_smoothSpaceTime hd j) x)
    (mem_extChartAt_target x) (show t ∈ Set.Icc 0 d.extendedT from
      ⟨ht.1, ht.2.trans hd.2.1.le⟩)
  have hu := (hd.2.2.2.1.1 x).contDiffAt (hOp.mem_nhds (mem_extChartAt_target x))
  have hprofile := (setup_wallProfiles hd).1.contDiffAt.comp (chartPt x x) (hu.div_const (d.A j))
  have hround : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hn : d.profileBase (d.u (chartInv x (chartPt x x)) / d.A j) ≠ 0 := by
    rwa [hround]
  exact hbase.add (((hprofile.inv hn).sub contDiffAt_const).const_smul (1 + s))

theorem updated_boundary_cost_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) (b : ℝ) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.T) (s : ℝ)
    (hδ : deltaBase d j (cotangentChartInv x z).1 ≠ 0)
    (hε : deltaFiber {d with B := Function.update d.B j b} j (cotangentChartInv x z) ≠ 0) :
    ContDiffAt ℝ 2 (fun w => dualNorm (d.h t) (cotangentChartInv x w).1 (cotangentChartInv x w).2 +
      wallCost {d with B := Function.update d.B j b} j (cotangentChartInv x w) t s) z := by
  have ht' : t ∈ Set.Icc 0 d.extendedT := ⟨ht.1, ht.2.trans hd.2.1.le⟩
  exact ((fiberNormModel_contDiffAt hd x hz ht').add
    ((fiberBaseModel_contDiffAt hd j x hz ht').add
      (((fiberBaseWallModel_contDiffAt hd j x hz hδ).add
        (updatedFiberWall_contDiffAt hd j x b hz hε)).const_smul (1 + s)))).of_le (by simp)

theorem norm_base_cost_contDiffAt {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {z : CotangentCoord n} (hz : z ∈ cotangentTarget x)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.T) (s : ℝ)
    (hδ : deltaBase d j (cotangentChartInv x z).1 ≠ 0) :
    ContDiffAt ℝ 2 (fun w => dualNorm (d.h t) (cotangentChartInv x w).1 (cotangentChartInv x w).2 +
      (baseCost d j (cotangentChartInv x w).1 t +
        (1 + s) * wallBase d j (cotangentChartInv x w).1)) z := by
  have ht' : t ∈ Set.Icc 0 d.extendedT := ⟨ht.1, ht.2.trans hd.2.1.le⟩
  exact ((fiberNormModel_contDiffAt hd x hz ht').add
    ((fiberBaseModel_contDiffAt hd j x hz ht').add
      ((fiberBaseWallModel_contDiffAt hd j x hz hδ).const_smul (1 + s)))).of_le (by simp)

end Yau.Blueprint.V04Proof.WallErrorAux
