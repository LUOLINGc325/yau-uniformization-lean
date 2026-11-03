import Yau.Proofs.F05BootstrapLocalBounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The actual within spatial Hessian is symmetric at the physical face.
Only supplied relative C2 regularity and accumulation by interior points
are used, before any joint higher regularity is asserted. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ}

theorem F05_posSpace_mem_closure_interior {ν : Option (RIdx n)} {x : Space n}
    (hx : x ∈ F05PosSpace ν) : x ∈ closure (interior (F05PosSpace ν)) := by
  have hn : ‖x‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx.2
  let R := (‖x‖+2)/2
  have hR : 0 < R := by dsimp only [R]; linarith [norm_nonneg x]
  have hR2 : R < 2 := by dsimp only [R]; linarith
  have hxR : x ∈ region ν R := F05_posSpace_mem_region hx (by dsimp only [R]; linarith)
  have hCl : x ∈ closure (interior (region ν R)) := by
    rw [F05_region_closure_interior ν hR]
    exact hxR
  exact closure_mono (interior_mono (F05_region_subset_posSpace ν hR2)) hCl

theorem F05_relative_hessian_symmetric {ν : Option (RIdx n)} {T : ℝ}
    {u : Point n → ℝ} (hu : F05RelC2 (F05PosSpace ν) (Ioc 0 T) u)
    {z : Point n} (hz : z ∈ F05PosPatch ν T) (v w : Space n) :
    F05RelDD (F05PosSpace ν) u z v w = F05RelDD (F05PosSpace ν) u z w v := by
  have hSymm := (hu.2.2.2.2.1 z.2 hz.2 z.1 hz.1).isSymmSndFDerivWithinAt (by simp)
    (F05_posSpace_uniqueDiffOn ν) (F05_posSpace_mem_closure_interior hz.1) hz.1
  exact hSymm.eq v w

end Yau.Proofs.F05Aux
