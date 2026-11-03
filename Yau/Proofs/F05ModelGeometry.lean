import Yau.Proofs.F05RegionGeometry
import Yau.Proofs.F05FlatRegions

/-! The model physical interior is an actual open half space or full space. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05ModelOpen_isOpen (A : AtlasData M) (i : Fin A.count) :
    IsOpen (F05ModelOpen A i) := by
  cases hν : A.normal i with
  | none => simpa only [F05ModelOpen,hν] using isOpen_univ
  | some j =>
    simp only [F05ModelOpen,hν]
    simpa only [realCoordLinear_apply] using
      (isOpen_lt (realCoordLinear j).continuous (continuous_const (y := (0 : ℝ))))

theorem F05D_interior_of_model (A : AtlasData M) (i : Fin A.count) {z : Space n}
    (hz : z ∈ F05ModelOpen A i) (hn : ‖z‖ < 2) : z ∈ interior (F05D A i) := by
  have hMem : z ∈ Metric.ball (0 : Space n) 2 ∩ F05ModelOpen A i :=
    ⟨by simpa only [Metric.mem_ball,dist_zero_right] using hn,hz⟩
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset ((Metric.isOpen_ball.inter (F05ModelOpen_isOpen A i)).mem_nhds hMem)
  intro w hw
  have hFace := subset_closure hw.2
  rw [F05ModelOpen_eq,F05FlatOpen_closure] at hFace
  exact ⟨(show ‖w‖ < 2 by simpa only [Metric.mem_ball,dist_zero_right] using hw.1).le,hFace⟩

end Yau.Proofs.F05Aux
