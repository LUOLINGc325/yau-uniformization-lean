import Yau.LeafProofs.L05PerturbationSpatialTransport
import Yau.LeafProofs.L05PerturbationPolynomials

open Set Metric Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_normalize_hessian {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1)
    {p : Point n} (hp : p ∈ backward 1) :
    hessian (perturbNormalize u z r N q0) p=(r^2/N) • hessian u (perturbCenter z r p) := by
  have he : (fun i j => spatialDD (perturbNormalize u z r N q0) p (realVec i) (realVec j) : Mat n)=
      (r^2/N) • (fun i j => spatialDD u (perturbCenter z r p) (realVec i) (realVec j) : Mat n) := by
    ext i j
    rw [perturb_normalize_spatialDD hu z hr hbuf hp]
    rfl
  unfold hessian sym
  rw [he]
  exact (selfAdjointPart ℝ).map_smul (r^2/N) _

theorem perturb_normalize_c2 {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 : ℝ} (hr : 0<r)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1) :
    C2 (backward 1) (perturbNormalize u z r N q0) := by
  have hm : MapsTo (perturbCenter z r) (backward 1) (backward 1) :=
    fun _ hp => perturb_center_mem_original hr hbuf hp
  have hc := (perturbCenter_continuous z r).continuousOn (s := backward 1)
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · have ht : ContinuousOn (fun p : Point n => r^2*q0*p.2) (backward 1) := by fun_prop
    exact (((hu.1.comp hc hm).sub continuousOn_const).sub ht).div_const N
  · exact ((hu.2.1.comp hc hm).const_smul (r/N)).congr
      (fun p hp => perturb_normalize_spatialD hu z hr hbuf hp)
  · exact ((hu.2.2.1.comp hc hm).const_smul (r^2/N)).congr
      (fun p hp => perturb_normalize_spatialDD hu z hr hbuf hp)
  · exact (((hu.2.2.2.1.comp hc hm).sub continuousOn_const).const_mul (r^2/N)).congr
      (fun p hp => perturb_normalize_timeD hu z hr hbuf hp)
  · intro p hp
    exact perturb_normalize_spatial_contDiffAt hu z hr hbuf hp
  · intro p hp
    have hh := (perturb_normalize_time_hasDerivWithinAt (N := N) (q0 := q0) hu z hr hbuf hp).differentiableWithinAt
    convert! hh using 1 <;> ext t <;> simp [backward,hp.1]

theorem perturb_affine_c2 {n : ℕ} {u : Point n → ℝ}
    (hu : C2 (backward 1) u) (z : Point n) {r N q0 : ℝ}
    (hr : 0<r) (_hN : 0<N)
    (hbuf : perturbClosed z.1 r z.2 ⊆ backward 1) :
    let v := fun p : Point n => (u (perturbCenter z r p)-u z-r^2*q0*p.2)/N
    C2 (backward 1) v ∧
      (∀ p ∈ backward 1, hessian v p=(r^2/N) • hessian u (perturbCenter z r p)) ∧
      (∀ p ∈ backward 1, spatialD v p=(r/N) • spatialD u (perturbCenter z r p)) ∧
      (∀ p ∈ backward 1, timeD (backward 1) v p=
        (r^2/N)*(timeD (backward 1) u (perturbCenter z r p)-q0)) := by
  exact ⟨perturb_normalize_c2 hu z hr hbuf,
    fun _ hp => perturb_normalize_hessian hu z hr hbuf hp,
    fun _ hp => perturb_normalize_spatialD hu z hr hbuf hp,
    fun _ hp => perturb_normalize_timeD hu z hr hbuf hp⟩

end Yau.LeafProofs.L05Aux
