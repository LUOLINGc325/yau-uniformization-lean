import Yau.LeafProofs.L05PerturbationScaleSpatial

open Filter MeasureTheory Set Metric
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_scaleValue_c2 {n : ℕ} {u : Point n → ℝ} (hu : C2 (backward 1) u)
    {r N : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : C2 (backward 1) (perturbScaleValue u r N) := by
  have hm : MapsTo (perturbScale (n := n) r) (backward 1) (backward 1) :=
    fun _ hp => perturb_scale_back_mem hr hr1 hp
  have hc := (perturbScale_continuous (n := n) r).continuousOn (s := backward 1)
  refine ⟨(hu.1.comp hc hm).div_const N,?_,?_,?_,?_,?_⟩
  · exact ((hu.2.1.comp hc hm).const_smul (r/N)).congr
      (fun p hp => perturb_scaleValue_spatialD hu hr hr1 hp)
  · exact ((hu.2.2.1.comp hc hm).const_smul (r^2/N)).congr
      (fun p hp => perturb_scaleValue_spatialDD hu hr hr1 hp)
  · exact ((hu.2.2.2.1.comp hc hm).const_mul (r^2/N)).congr
      (fun p hp => perturb_scaleValue_timeD hu hr hr1 hp)
  · intro p hp
    exact perturb_scaleValue_spatial_contDiffAt hu hr hr1 hp
  · intro p hp
    have hd := (perturb_scaleValue_time_hasDerivWithinAt (N := N) hu hr hr1 hp).differentiableWithinAt
    convert! hd using 1 <;> ext t <;> simp [backward,hp.1]

theorem perturb_scaleValue_hessian {n : ℕ} {u : Point n → ℝ} (hu : C2 (backward 1) u)
    {r N : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {p : Point n} (hp : p∈backward 1) :
    hessian (perturbScaleValue u r N) p=(r^2/N) • hessian u (perturbScale r p) := by
  have he : (fun i j => spatialDD (perturbScaleValue u r N) p (realVec i) (realVec j) : Mat n)=
      (r^2/N) • (fun i j => spatialDD u (perturbScale r p) (realVec i) (realVec j) : Mat n) := by
    ext i j
    rw [perturb_scaleValue_spatialDD hu hr hr1 hp]
    rfl
  unfold hessian sym
  rw [he]
  exact (selfAdjointPart ℝ).map_smul (r^2/N) _

end Yau.LeafProofs.L05Aux
