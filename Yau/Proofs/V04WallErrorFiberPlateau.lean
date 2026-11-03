import Yau.Proofs.V04WallErrorPlateau
import Yau.Proofs.V03MetricSmooth

/-! The original fiber wall is identically zero on a genuine chart
neighborhood whenever the chosen fiber cutoff is below one. -/

open Filter
open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {n q : ℕ} {X : KahlerManifold n}

theorem fiberWall_eq_zero_near {d : VariationData X q} (hp : WallProfiles d)
    (hh0 : d.h 0 = X.metric.form) (j : ℕ) (hB : 0 < d.B j)
    (Ccoeff : ℕ → ℝ) (y : CotangentPoint X.manifold)
    (hcut : clockFiberCutoff d (chosenClockData X Ccoeff) j y ≠ 1) :
    (fun z => wallFiber d j (cotangentChartInv y.1 z)) =ᶠ[𝓝 (cotangentChart y.1 y)] (fun _ => 0) := by
  have hlt : fiberClockProfile (dualNorm (d.h 0) y.1 y.2 / d.B j ^ 2) < 1 :=
    lt_of_le_of_ne (fiberClockProfile_bounds _).2 hcut
  obtain ⟨V, hV, hyV, hprofile⟩ := fiber_wall_profile_constant_near hp hlt
  have hopen : IsOpen (cotangentTarget y.1) :=
    (isOpen_extChartAt_target (I := ComplexModel n) y.1).prod isOpen_univ
  have hyself : y ∈ cotangentSource y.1 := mem_extChartAt_source y.1
  have hyT := cotangentChart_mapsTo y.1 hyself
  have hround := cotangentChart_left_inv y.1 hyself
  have hnorm : ContDiffOn ℝ ∞
      (fun z => dualNorm (d.h 0) (cotangentChartInv y.1 z).1 (cotangentChartInv y.1 z).2)
      (cotangentTarget y.1) := by
    rw [hh0]
    exact (dualNormChart_contDiffOn X.metric y.1).congr
      (fun z hz => dualNorm_cotangentChartInv X.metric.form y.1 hz)
  have hu : ContinuousAt
      (fun z => dualNorm (d.h 0) (cotangentChartInv y.1 z).1 (cotangentChartInv y.1 z).2 / d.B j ^ 2)
      (cotangentChart y.1 y) :=
    (hnorm.continuousOn.continuousAt (hopen.mem_nhds hyT)).div_const _
  have hv : ∀ᶠ z in 𝓝 (cotangentChart y.1 y),
      dualNorm (d.h 0) (cotangentChartInv y.1 z).1 (cotangentChartInv y.1 z).2 / d.B j ^ 2 ∈ V := by
    apply hu.eventually
    change V ∈ 𝓝 (dualNorm (d.h 0) (cotangentChartInv y.1 (cotangentChart y.1 y)).1
      (cotangentChartInv y.1 (cotangentChart y.1 y)).2 / d.B j ^ 2)
    rw [hround]
    exact hV.mem_nhds hyV
  filter_upwards [hv] with z hz
  simp only [wallFiber, deltaFiber, hprofile _ hz, inv_one, sub_self]

theorem fiberWall_spatialHessian_eq_zero_of_cutoff_ne_one {d : VariationData X q}
    (hp : WallProfiles d) (hh0 : d.h 0 = X.metric.form) (j : ℕ) (hB : 0 < d.B j)
    (Ccoeff : ℕ → ℝ) (y : CotangentPoint X.manifold)
    (hcut : clockFiberCutoff d (chosenClockData X Ccoeff) j y ≠ 1) :
    spatialHessian (wallFiber d j) y = 0 := by
  have heq := leviMatrix_congr_of_eventuallyEq (fiberWall_eq_zero_near hp hh0 j hB Ccoeff y hcut) cotangentDir
  simpa only [spatialHessian, leviMatrix_const] using heq

theorem spatialHessian_add_flat_fiberWall {d : VariationData X q}
    (hp : WallProfiles d) (hh0 : d.h 0 = X.metric.form) (j : ℕ) (hB : 0 < d.B j)
    (Ccoeff : ℕ → ℝ) (y : CotangentPoint X.manifold)
    (hcut : clockFiberCutoff d (chosenClockData X Ccoeff) j y ≠ 1)
    (f : CotangentPoint X.manifold → ℝ) (s : ℝ) :
    spatialHessian (fun y' => f y' + s * wallFiber d j y') y = spatialHessian f y := by
  have heq : (fun z => f (cotangentChartInv y.1 z) + s * wallFiber d j (cotangentChartInv y.1 z)) =ᶠ[𝓝 (cotangentChart y.1 y)]
      (fun z => f (cotangentChartInv y.1 z)) := by
    filter_upwards [fiberWall_eq_zero_near hp hh0 j hB Ccoeff y hcut] with z hz
    rw [hz, mul_zero, add_zero]
  exact leviMatrix_congr_of_eventuallyEq heq cotangentDir

end Yau.Blueprint.V04Proof.WallErrorAux
