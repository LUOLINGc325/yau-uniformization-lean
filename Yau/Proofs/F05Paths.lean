import Yau.Proofs.F05AtlasModel
import Yau.LeafProofs.L16

/-! Genuine continuous segment and time paths in the closed chart cylinders. -/

open Set
open scoped Topology
noncomputable section

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05D_convex (A : AtlasData M) (i : Fin A.count) : Convex ℝ (F05D A i) := by
  cases hν : A.normal i with
  | none =>
    have heq : F05D A i = Metric.closedBall (0 : Space n) 2 := by
      ext z
      simp [F05D,region,hν,Metric.mem_closedBall,dist_zero_right]
    rw [heq]
    exact convex_closedBall 0 2
  | some j =>
    have heq : F05D A i = Metric.closedBall (0 : Space n) 2 ∩
        {z | realCoordLinear j z ≤ 0} := by
      ext z
      simp [F05D,region,hν,Metric.mem_closedBall,dist_zero_right,realCoordLinear_apply]
    rw [heq]
    exact (convex_closedBall 0 2).inter
      (convex_halfSpace_le (realCoordLinear j).toLinearMap.isLinear 0)

def F05SpatialPath (A : AtlasData M) (i : Fin A.count) (T : ℝ)
    {z w : Space n} (hz : z ∈ F05D A i) (hw : w ∈ F05D A i)
    {t : ℝ} (ht : t ∈ Icc 0 T) (r : ℝ) : F05Q A i T :=
  ⟨(AffineMap.lineMap z w (projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) r).val,t),
    (F05D_convex A i).lineMap_mem hz hw (projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) r).property,ht⟩

theorem F05SpatialPath_continuous (A : AtlasData M) (i : Fin A.count) (T : ℝ)
    {z w : Space n} (hz : z ∈ F05D A i) (hw : w ∈ F05D A i)
    {t : ℝ} (ht : t ∈ Icc 0 T) : Continuous (F05SpatialPath A i T hz hw ht) := by
  apply Continuous.subtype_mk
  change Continuous (fun r : ℝ =>
    (AffineMap.lineMap z w (projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) r).val,t))
  fun_prop

theorem F05SpatialPath_eq (A : AtlasData M) (i : Fin A.count) (T : ℝ)
    {z w : Space n} (hz : z ∈ F05D A i) (hw : w ∈ F05D A i)
    {t : ℝ} (ht : t ∈ Icc 0 T) {r : ℝ} (hr : r ∈ Icc 0 1) :
    (F05SpatialPath A i T hz hw ht r).val = (AffineMap.lineMap z w r,t) := by
  simp only [F05SpatialPath,projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) hr]

def F05TimePath (A : AtlasData M) (i : Fin A.count) {T : ℝ} (hT : 0 ≤ T)
    {z : Space n} (hz : z ∈ F05D A i) (r : ℝ) : F05Q A i T :=
  ⟨(z,(projIcc 0 T hT r).val),hz,(projIcc 0 T hT r).property⟩

theorem F05TimePath_continuous (A : AtlasData M) (i : Fin A.count) {T : ℝ} (hT : 0 ≤ T)
    {z : Space n} (hz : z ∈ F05D A i) : Continuous (F05TimePath A i hT hz) := by
  apply Continuous.subtype_mk
  change Continuous (fun r : ℝ => (z,(projIcc 0 T hT r).val))
  fun_prop

theorem F05TimePath_eq (A : AtlasData M) (i : Fin A.count) {T : ℝ} (hT : 0 ≤ T)
    {z : Space n} (hz : z ∈ F05D A i) {r : ℝ} (hr : r ∈ Icc 0 T) :
    (F05TimePath A i hT hz r).val = (z,r) := by
  simp only [F05TimePath,projIcc_of_mem hT hr]

end Yau.Proofs.F05Aux
