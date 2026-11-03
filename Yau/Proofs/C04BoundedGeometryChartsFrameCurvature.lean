import Yau.Proofs.C04BoundedGeometryChartsFrameConnection
import Yau.LeafProofs.L23DistanceEnergyCovariant

/-! Curvature transforms by the actual moving frame and the actual differential of the map. -/

noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

theorem mapCovariantD_congr_local
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z f g : ComplexVector n → ComplexVector n) (v a : ComplexVector n)
    (heq : f =ᶠ[𝓝 v] g) : mapCovariantD Γ Z a f v = mapCovariantD Γ Z a g v := by
  simp only [mapCovariantD, mapDirection, heq.fderiv_eq, heq.self_of_nhds]

theorem coordinateFrameConnection_covariantD
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z : ComplexVector n → ComplexVector n)
    (P : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (V : ComplexVector n → ComplexVector n) (v u : ComplexVector n)
    (hP : DifferentiableAt ℝ P v) (hV : DifferentiableAt ℝ V v) (hiP : (P v).IsInvertible) :
    mapCovariantD Γ Z u (fun z => P z (V z)) v =
      P v (fderiv ℝ V v u + coordinateFrameConnection Γ Z P v u (V v)) := by
  rw [mapCovariantD, mapDirection, fderiv_clm_apply hP hV]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, map_add,
    coordinateFrameConnection_equation Γ Z P v u (V v) hiP]
  simp only [mapDirection]
  abel

theorem coordinateFrameConnection_curvature
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (Z : ComplexVector n → ComplexVector n)
    (P : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
    (v u w z : ComplexVector n)
    (hΓ : ContDiffAt ℝ ∞ Γ (Z v)) (hZ : ContDiffAt ℝ ∞ Z v)
    (hP : ContDiffAt ℝ ∞ P v) (hiP : (P v).IsInvertible) :
    P v (connectionCurvature (coordinateFrameConnection Γ Z P) v u w z) =
      connectionCurvature Γ (Z v) (fderiv ℝ Z v u) (fderiv ℝ Z v w) (P v z) := by
  let conn := coordinateFrameConnection Γ Z P
  have hconn : ContDiffAt ℝ ∞ conn v := coordinateFrameConnection_smoothAt Γ Z P v hΓ hZ hP hiP
  have hPd : ∀ᶠ x in 𝓝 v, DifferentiableAt ℝ P x :=
    ((hP.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)).mono
      (fun _ hx => hx.differentiableAt_one)
  have hPi : ∀ᶠ x in 𝓝 v, (P x).IsInvertible :=
    hP.continuousAt.eventually hiP.eventually_nhds
  have hInner (a : ComplexVector n) : mapCovariantD Γ Z a (fun x => P x z) =ᶠ[𝓝 v]
      (fun x => P x (conn x a z)) := by
    filter_upwards [hPd, hPi] with x hx hi
    have H := coordinateFrameConnection_covariantD Γ Z P (fun _ => z) x a hx (differentiableAt_const z) hi
    simpa only [fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_add] using H
  have hOuter (a b : ComplexVector n) :
      mapCovariantD Γ Z a (mapCovariantD Γ Z b (fun x => P x z)) v =
        P v (mapCovariantD conn id a (fun x => conn x b z) v) := by
    rw [mapCovariantD_congr_local Γ Z _ _ v a (hInner b)]
    have hV : DifferentiableAt ℝ (fun x => conn x b z) v :=
      ((hconn.clm_apply (contDiffAt_const (c := b))).clm_apply (contDiffAt_const (c := z))).differentiableAt (by simp)
    have H := coordinateFrameConnection_covariantD Γ Z P (fun x => conn x b z) v a
      (hP.differentiableAt (by simp)) hV hiP
    simpa only [mapCovariantD, mapDirection, fderiv_id, ContinuousLinearMap.id_apply, id_eq] using H
  have HΓ := mapCovariantD_commutator Γ Z (fun x => P x z)
    (hΓ.differentiableAt (by simp)) (hZ.of_le (by simp))
    ((hP.clm_apply (contDiffAt_const (c := z))).of_le (by simp)) u w
  rw [hOuter, hOuter, ← map_sub] at HΓ
  have Hconn := mapCovariantD_commutator conn (id : ComplexVector n → ComplexVector n) (fun _ => z)
    (hconn.differentiableAt (by simp)) (contDiffAt_id (n := 2)) (contDiffAt_const (n := 2)) u w
  have hInnerconn (a : ComplexVector n) : mapCovariantD conn id a (fun _ => z) = (fun x => conn x a z) := by
    funext x
    simp only [mapCovariantD, mapDirection, fderiv_const_apply, ContinuousLinearMap.zero_apply,
      fderiv_id, ContinuousLinearMap.id_apply, zero_add, id_eq]
  rw [hInnerconn, hInnerconn] at Hconn
  simp only [mapDirection, fderiv_id, ContinuousLinearMap.id_apply, id_eq] at Hconn
  rw [Hconn] at HΓ
  exact HΓ

end Yau.Proofs.C04ChartsAux
