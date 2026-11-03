import Yau.Proofs.V04WallErrorFiberNormalize
import Yau.Proofs.V04WallErrorFiberPlateau
import Yau.Proofs.V04WallErrorBase

/-! The two original wall-error contracts hold for one choice of
coefficients, chosen at every index before all admissible radii. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem fiberErrorScalar_zero_of_cutoff_ne_one {d : VariationData X q}
    (hd : VariationSetup d) (j : ℕ) {b : ℝ} (hb : 0 < b)
    (Ccoeff : ℕ → ℝ) (y : CotangentPoint X.manifold)
    (hy : y ∈ boundaryRegion {d with B := Function.update d.B j b} j)
    {t : ℝ} (ht : t ∈ Set.Icc 0 d.T) (s : ℝ)
    (hcut : clockFiberCutoff {d with B := Function.update d.B j b}
      (chosenClockData X Ccoeff) j y ≠ 1) :
    fiberErrorScalar {d with B := Function.update d.B j b} j y t s = 0 := by
  let db := {d with B := Function.update d.B j b}
  have hp : WallProfiles db := setup_wallProfiles (d := d) hd
  have hb' : 0 < db.B j := by simpa only [db, Function.update_self] using hb
  have hflat := spatialHessian_add_flat_fiberWall hp hd.2.2.1.1.1.1 j hb' Ccoeff y hcut
    (fun v => dualNorm (d.h t) v.1 v.2 +
      (baseCost d j v.1 t + (1 + s) * wallBase d j v.1)) (1 + s)
  have hfun : (fun v => dualNorm (d.h t) v.1 v.2 + wallCost db j v t s) =
      (fun v => (dualNorm (d.h t) v.1 v.2 +
        (baseCost d j v.1 t + (1 + s) * wallBase d j v.1)) + (1 + s) * wallFiber db j v) := by
    funext v
    change dualNorm (d.h t) v.1 v.2 +
      (baseCost d j v.1 t + (1 + s) * (wallBase d j v.1 + wallFiber db j v)) = _
    ring
  have hδ : deltaBase d j y.1 ≠ 0 :=
    (deltaBase_pos (setup_wallProfiles hd) (setup_index_bounds hd j).1 hy.1).ne'
  have hcore := krf_symplecticP_dualNorm_add_base hd.2.2.1.1.1 ht.1 y
    (fun w => baseCost d j w t + (1 + s) * wallBase d j w)
    (baseCost_wall_inChart_contDiffAt hd j y.1 ht s hδ)
  change symplecticP (spatialHessian (fun v => dualNorm (d.h t) v.1 v.2 + wallCost db j v t s) y) -
    derivWithin (fun τ => dualNorm (d.h τ) y.1 y.2) (Set.Ici 0) t -
      laplacian (d.h t) (fun w => baseCost d j w t + (1 + s) * wallBase d j w) y.1 = 0
  rw [hfun, hflat, hcore]
  ring

theorem exists_chosen_wall_errors {d : VariationData X q} (hd : VariationSetup d) :
    ∃ C : ℕ → ℝ, (∀ j, 1 ≤ C j) ∧
      FiberWallError d (chosenClockData X C) ∧ BaseWallError d (chosenClockData X C) := by
  choose C hC using fun j => exists_fiber_uniform_bound hd j
  refine ⟨C, (fun j => (hC j).1), ?_, baseWallError_chosenClockData hd C⟩
  intro j b hb
  dsimp only
  intro y hy t ht s hs
  change |fiberErrorScalar {d with B := Function.update d.B j b} j y t s| ≤
    C j * (1 + b) ^ 6 *
      (wallProduct {d with B := Function.update d.B j b} j y ^ 6)⁻¹ *
        (if clockFiberCutoff {d with B := Function.update d.B j b}
          (chosenClockData X C) j y = 1 then 1 else 0)
  by_cases hcut : clockFiberCutoff {d with B := Function.update d.B j b}
      (chosenClockData X C) j y = 1
  · simpa only [if_pos hcut, mul_one] using (hC j).2 b hb y hy t ht s hs
  · rw [fiberErrorScalar_zero_of_cutoff_ne_one hd j
      (zero_lt_one.trans_le (one_le_admissible_radius hb)) C y hy ht s hcut,
      abs_zero, if_neg hcut, mul_zero]

end Yau.Blueprint.V04Proof.WallErrorAux
