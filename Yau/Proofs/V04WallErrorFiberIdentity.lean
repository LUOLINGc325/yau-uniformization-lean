import Yau.Proofs.V04WallErrorFiberHessianScaling
import Yau.Proofs.V04WallErrorSymplecticInvariant

/-! The cleared polynomial is the original physical fiber-wall error,
computed in a genuine fixed cotangent chart. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n q : ℕ} {X : KahlerManifold n}

def fiberErrorScalar (d : VariationData X q) (j : ℕ)
    (y : CotangentPoint X.manifold) (t s : ℝ) : ℝ :=
  symplecticP (spatialBoundaryHessianAt d j y t s) -
    derivWithin (fun τ => dualNorm (d.h τ) y.1 y.2) (Set.Ici 0) t -
      laplacian (d.h t) (fun x => baseCost d j x t + (1 + s) * wallBase d j x) y.1

theorem fiberErrorScalar_eq_chart_difference {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (b : ℝ) (x : Pt X) {y : CotangentPoint X.manifold}
    (hy : y ∈ cotangentSource x) {t : ℝ} (ht : t ∈ Set.Icc 0 d.T) (s : ℝ)
    (hδ : deltaBase d j y.1 ≠ 0)
    (hε : deltaFiber {d with B := Function.update d.B j b} j y ≠ 0) :
    fiberErrorScalar {d with B := Function.update d.B j b} j y t s =
      symplecticP (leviMatrix (fun w => dualNorm (d.h t) (cotangentChartInv x w).1
        (cotangentChartInv x w).2 + wallCost {d with B := Function.update d.B j b} j
          (cotangentChartInv x w) t s) (cotangentChart x y) cotangentDir) -
      symplecticP (leviMatrix (fun w => dualNorm (d.h t) (cotangentChartInv x w).1
        (cotangentChartInv x w).2 + (baseCost d j (cotangentChartInv x w).1 t +
          (1 + s) * wallBase d j (cotangentChartInv x w).1)) (cotangentChart x y) cotangentDir) := by
  let G : CotangentPoint X.manifold → ℝ := fun v =>
    dualNorm (d.h t) v.1 v.2 + wallCost {d with B := Function.update d.B j b} j v t s
  let G₀ : CotangentPoint X.manifold → ℝ := fun v =>
    dualNorm (d.h t) v.1 v.2 + (baseCost d j v.1 t + (1 + s) * wallBase d j v.1)
  have hround := cotangentChart_left_inv x hy
  have hz := cotangentChart_mapsTo x hy
  have hδz : deltaBase d j (cotangentChartInv x (cotangentChart x y)).1 ≠ 0 := by
    rwa [hround]
  have hεz : deltaFiber {d with B := Function.update d.B j b} j
      (cotangentChartInv x (cotangentChart x y)) ≠ 0 := by rwa [hround]
  have hG := symplecticP_spatialHessian_fixed_chart G x hy
    (updated_boundary_cost_contDiffAt hd j x b hz ht s hδz hεz)
  have hG₀ := symplecticP_spatialHessian_fixed_chart G₀ x hy
    (norm_base_cost_contDiffAt hd j x hz ht s hδz)
  have hcore := krf_symplecticP_dualNorm_add_base hd.2.2.1.1.1 ht.1 y
    (fun w => baseCost d j w t + (1 + s) * wallBase d j w)
    (baseCost_wall_inChart_contDiffAt hd j y.1 ht s hδ)
  have herr : fiberErrorScalar {d with B := Function.update d.B j b} j y t s =
      symplecticP (spatialHessian G y) - symplecticP (spatialHessian G₀ y) := by
    change symplecticP (spatialHessian G y) -
      derivWithin (fun τ => dualNorm (d.h τ) y.1 y.2) (Set.Ici 0) t -
      laplacian (d.h t) (fun w => baseCost d j w t + (1 + s) * wallBase d j w) y.1 = _
    change symplecticP (spatialHessian G₀ y) = _ + _ at hcore
    rw [hcore]
    ring
  exact herr.trans (congrArg₂ (fun u v : ℝ => u - v) hG hG₀)

theorem fiber_error_cleared_identity {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {b : ℝ} (hb : b ≠ 0) {z : CotangentCoord n}
    (hz : z ∈ cotangentTarget x) {t : ℝ} (ht : t ∈ Set.Icc 0 d.T) (s : ℝ)
    (hδ : deltaBase d j (cotangentChartInv x z).1 ≠ 0)
    (hε : normalizedFiberProfile d x z ≠ 0) :
    wallProduct {d with B := Function.update d.B j b} j
        (cotangentChartInv x (fiberDilation b z)) ^ 6 *
      fiberErrorScalar {d with B := Function.update d.B j b} j
        (cotangentChartInv x (fiberDilation b z)) t s =
    clearedFiberPolynomial
      (leviMatrix (fiberNormModel d x t) z cotangentDir)
      (leviMatrix (fiberBaseModel d j x t) z cotangentDir)
      (fiberBaseCleared d j x z) (fiberFiberCleared d x z)
      (deltaBase d j (cotangentChartInv x z).1) (normalizedFiberProfile d x z) b⁻¹ (1 + s) := by
  have hzB : fiberDilation b z ∈ cotangentTarget x := ⟨hz.1, Set.mem_univ _⟩
  have hεB : deltaFiber {d with B := Function.update d.B j b} j
      (cotangentChartInv x (fiberDilation b z)) ≠ 0 := by
    rwa [deltaFiber_update_dilation d j x hb z]
  have herr := fiberErrorScalar_eq_chart_difference hd j b x
    (cotangentChartInv_mapsTo x hzB) ht s hδ hεB
  rw [cotangentChart_right_inv x hzB] at herr
  rw [herr, fiber_rescaled_hessian_difference hd j x hb hz ht s hδ hε]
  have hprod : wallProduct {d with B := Function.update d.B j b} j
      (cotangentChartInv x (fiberDilation b z)) =
      deltaBase d j (cotangentChartInv x z).1 * normalizedFiberProfile d x z := by
    unfold wallProduct
    rw [deltaFiber_update_dilation d j x hb z]
    rfl
  rw [hprod, fiberBaseCleared_eq hd j x hz hδ, fiberFiberCleared_eq hd x hz hε]
  exact (clearedFiberPolynomial_eq _ _ _ _ _ _ _ _).symm

end Yau.Blueprint.V04Proof.WallErrorAux
