import Yau.LeafProofs.L05PerturbationSpatialTransport

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_center_spatialD_map {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (z : Point n) (r : ℝ) {p : Point n} (hp : perturbCenter z r p∈Q) :
    spatialD (fun q => u (perturbCenter z r q)) p=r • spatialD u (perturbCenter z r p) := by
  let L : Space n →L[ℝ] Space n := r • ContinuousLinearMap.id ℝ (Space n)
  have hMap : HasFDerivAt (fun x : Space n => z.1+r • x) L p.1 := by
    convert! L.hasFDerivAt.const_add z.1 using 1
  have hOrig := (hu.2.2.2.2.1 _ hp).differentiableAt (by norm_num)
  have hDeriv := hOrig.hasFDerivAt.comp p.1 hMap
  change fderiv ℝ (fun x => u (z.1+r • x,z.2+r^2*p.2)) p.1= _
  have hFD := hDeriv.fderiv
  simp only [Function.comp_def,perturbCenter] at hFD
  rw [hFD]
  ext v
  simp only [L,ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,
    map_smul,spatialD,perturbCenter]

theorem perturb_center_spatialDD_map {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (z : Point n) (r : ℝ) {p : Point n} (hp : perturbCenter z r p∈Q) :
    spatialDD (fun q => u (perturbCenter z r q)) p=r^2 • spatialDD u (perturbCenter z r p) := by
  exact perturb_space_second_scale z.1 r (hu.2.2.2.2.1 _ hp)

theorem perturb_center_hessian_map {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (z : Point n) (r : ℝ) {p : Point n} (hp : perturbCenter z r p∈Q) :
    hessian (fun q => u (perturbCenter z r q)) p=r^2 • hessian u (perturbCenter z r p) := by
  have he : (fun i j => spatialDD (fun q => u (perturbCenter z r q)) p (realVec i) (realVec j) : Mat n)=
      r^2 • (fun i j => spatialDD u (perturbCenter z r p) (realVec i) (realVec j) : Mat n) := by
    ext i j
    rw [perturb_center_spatialDD_map hu z r hp]
    rfl
  unfold hessian sym
  rw [he]
  exact (selfAdjointPart ℝ).map_smul (r^2) _

theorem perturb_center_time_hasDeriv_map {n : ℕ} {Q P : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (z : Point n) (r : ℝ) (hMap : MapsTo (perturbCenter z r) P Q)
    {p : Point n} (hp : p∈P) :
    HasDerivWithinAt (fun t => u (perturbCenter z r (p.1,t)))
      (r^2*timeD Q u (perturbCenter z r p)) {t : ℝ | (p.1,t)∈P} p.2 := by
  have hOrig := (hu.2.2.2.2.2 _ (hMap hp)).hasDerivWithinAt
  change HasDerivWithinAt (fun t => u (z.1+r • p.1,t))
    (timeD Q u (perturbCenter z r p)) {t : ℝ | (z.1+r • p.1,t)∈Q} (z.2+r^2*p.2) at hOrig
  have hTime := ((hasDerivAt_id p.2).const_mul (r^2)).const_add z.2
  have hFiber : MapsTo (fun t : ℝ => z.2+r^2*t) {t : ℝ | (p.1,t)∈P}
      {t : ℝ | (z.1+r • p.1,t)∈Q} := fun t ht => hMap ht
  have hDeriv := hOrig.comp p.2 hTime.hasDerivWithinAt hFiber
  simpa only [Function.comp_def,perturbCenter,id_eq,mul_one,mul_comm] using hDeriv

theorem perturb_center_timeD_map {n : ℕ} {Q P : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (z : Point n) (r : ℝ) (hMap : MapsTo (perturbCenter z r) P Q)
    {p : Point n} (hp : p∈P)
    (hUnique : UniqueDiffWithinAt ℝ {t : ℝ | (p.1,t)∈P} p.2) :
    timeD P (fun q => u (perturbCenter z r q)) p=r^2*timeD Q u (perturbCenter z r p) :=
  (perturb_center_time_hasDeriv_map hu z r hMap hp).derivWithin hUnique

theorem perturb_center_c2_map {n : ℕ} {Q P : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) (z : Point n) (r : ℝ) (hMap : MapsTo (perturbCenter z r) P Q)
    (hUnique : ∀ p∈P, UniqueDiffWithinAt ℝ {t : ℝ | (p.1,t)∈P} p.2) :
    C2 P (fun q => u (perturbCenter z r q)) := by
  have hCont : ContinuousOn (perturbCenter z r) P := (perturbCenter_continuous z r).continuousOn
  refine ⟨hu.1.comp hCont hMap,?_,?_,?_,?_,?_⟩
  · exact ((hu.2.1.comp hCont hMap).const_smul r).congr
      (fun p hp => perturb_center_spatialD_map hu z r (hMap hp))
  · exact ((hu.2.2.1.comp hCont hMap).const_smul (r^2)).congr
      (fun p hp => perturb_center_spatialDD_map hu z r (hMap hp))
  · exact ((hu.2.2.2.1.comp hCont hMap).const_mul (r^2)).congr
      (fun p hp => perturb_center_timeD_map hu z r hMap hp (hUnique p hp))
  · intro p hp
    have hSource : ContDiffAt ℝ 2 (fun x : Space n => u (x,z.2+r^2*p.2)) (z.1+r • p.1) :=
      hu.2.2.2.2.1 _ (hMap hp)
    have hPull := hSource.comp p.1 (show ContDiffAt ℝ 2 (fun x : Space n => z.1+r • x) p.1 from
      contDiffAt_const.add (contDiffAt_id.const_smul r))
    simpa only [Function.comp_def,perturbCenter] using hPull
  · intro p hp
    exact (perturb_center_time_hasDeriv_map hu z r hMap hp).differentiableWithinAt

end Yau.LeafProofs.L05Aux
