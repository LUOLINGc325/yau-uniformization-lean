import Yau.Proofs.F05CoordinateCoefficients
import Yau.Proofs.F05MatrixCalculus

/-! Smoothness of the computed flattened principal matrix and full drift
follows from the actual metric family and actual chart derivatives. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.ParabolicCandidates Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_flatSmoothFirstGroup : NormedAddCommGroup (Space n →L[ℝ] Space n) := inferInstance
local instance f05_flatSmoothFirstSpace : NormedSpace ℝ (Space n →L[ℝ] Space n) := inferInstance
local instance f05_flatSmoothSecondGroup : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance
local instance f05_flatSmoothSecondSpace : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] Space n) := inferInstance

theorem F05_spatial_chart_jets_smooth {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ (A.forward i) (A.inverse i z)) (Metric.ball 0 3) ∧
      ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fderiv ℝ (A.forward i)) (A.inverse i z)) (Metric.ball 0 3) := by
  have hAt (z : Space n) (hz : z ∈ Metric.ball 0 3) :
      ContDiffAt ℝ ∞ (A.forward i) (A.inverse i z) :=
    ((hA.1 i).2.2.1).contDiffAt ((hA.1 i).1.mem_nhds ((hA.1 i).2.2.2.2.1 ⟨z,hz,rfl⟩))
  have hInv (z : Space n) (hz : z ∈ Metric.ball 0 3) : ContDiffAt ℝ ∞ (A.inverse i) z :=
    ((hA.1 i).2.2.2.1).contDiffAt (Metric.isOpen_ball.mem_nhds hz)
  constructor
  · intro z hz
    exact (((hAt z hz).fderiv_right (m := ∞) (by simp)).comp z (hInv z hz)).contDiffWithinAt
  · intro z hz
    have hD := (hAt z hz).fderiv_right (m := ∞) (by simp)
    have hDD := hD.fderiv_right (m := ∞) (by simp)
    exact (hDD.comp z (hInv z hz)).contDiffWithinAt

theorem F05_flat_coefficients_smooth {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {I : Set ℝ}
    (hh : MetricFamilySmooth h I) (i : Fin A.count) :
    SmoothCoefficients (Metric.ball 0 3 ×ˢ I)
      (fun p => flatA (h p.2) A i p) (fun p => flatB (h p.2) A i p) := by
  have hProduct : SmoothCoefficients (Metric.ball 0 3 ×ˢ I)
      (fun p => flatA (h p.2) A i p) (fun p => flatB (h p.2) A i p) := by
    let Q : Set (Point n) := Metric.ball 0 3 ×ˢ I
    let L : Point n → Space n →L[ℝ] Space n := fun p => fderiv ℝ (A.forward i) (A.inverse i p.1)
    let B : Point n → Space n →L[ℝ] Space n →L[ℝ] Space n :=
      fun p => fderiv ℝ (fderiv ℝ (A.forward i)) (A.inverse i p.1)
    let a : Point n → Mat n := fun p => baseA (h p.2) (A.center i) (A.inverse i p.1)
    have hMap (p : Point n) (hp : p ∈ Q) : (A.inverse i p.1,p.2) ∈ chartTarget (A.center i) ×ˢ I :=
      ⟨(hA.1 i).2.1 ((hA.1 i).2.2.2.2.1 ⟨p.1,hp.1,rfl⟩),hp.2⟩
    have hInverse : ContDiffOn ℝ ∞ (fun p : Point n => (A.inverse i p.1,p.2)) Q :=
      (((hA.1 i).2.2.2.1).comp contDiffOn_fst (fun p hp => hp.1)).prodMk contDiffOn_snd
    have hBase := ((Yau.F04Proof.flowChartPrincipal_smooth h hh (A.center i)).1).comp hInverse hMap
    have ha : ContDiffOn ℝ ∞ a Q := hBase.congr (fun p hp =>
      F05_baseA_eq_flowChartPrincipal h (A.center i) (hMap p hp).1 p.2)
    have hGeometry := F05_spatial_chart_jets_smooth hA i
    have hL : ContDiffOn ℝ ∞ L Q := hGeometry.1.comp contDiffOn_fst (fun p hp => hp.1)
    have hB : ContDiffOn ℝ ∞ B Q := hGeometry.2.comp contDiffOn_fst (fun p hp => hp.1)
    have hLC (j k : RIdx n) : ContDiffOn ℝ ∞ (fun p => realCoord (L p (realVec j)) k) Q := by
      let E : (Space n →L[ℝ] Space n) →L[ℝ] ℝ :=
        (realCoordLinear k).comp (ContinuousLinearMap.apply ℝ (Space n) (realVec j))
      simpa only [E,Function.comp_def,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply,realCoordLinear_apply] using
        E.contDiff.contDiffOn.comp hL (fun _ _ => mem_univ _)
    have hBC (j k l : RIdx n) :
        ContDiffOn ℝ ∞ (fun p => realCoord (B p (realVec j) (realVec k)) l) Q := by
      let E : (Space n →L[ℝ] Space n →L[ℝ] Space n) →L[ℝ] ℝ :=
        (realCoordLinear l).comp ((ContinuousLinearMap.apply ℝ (Space n) (realVec k)).comp
          (ContinuousLinearMap.apply ℝ (Space n →L[ℝ] Space n) (realVec j)))
      simpa only [E,Function.comp_def,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply,realCoordLinear_apply] using
        E.contDiff.contDiffOn.comp hB (fun _ _ => mem_univ _)
    have hPrincipal : ContDiffOn ℝ ∞ (fun p => chartPrincipalMatrix (L p) (a p)) Q := by
      apply Yau.F04Proof.matrix_contDiffOn_of_entries
      intro k l
      change ContDiffOn ℝ ∞ (fun p => ∑ j, ∑ e,
        a p j e * realCoord (L p (realVec j)) k * realCoord (L p (realVec e)) l) Q
      exact ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun e _ =>
        ((F05_contDiffOn_matrix_entry ha j e).mul (hLC j k)).mul (hLC e l)))
    have hDrift (k : RIdx n) :
        ContDiffOn ℝ ∞ (fun p => chartDriftVector (L p) (B p) (a p) (fun _ => 0) k) Q := by
      simp only [chartDriftVector,zero_mul,Finset.sum_const_zero,add_zero]
      exact ContDiffOn.sum (fun j _ => ContDiffOn.sum (fun e _ =>
        (F05_contDiffOn_matrix_entry ha j e).mul (hBC j e k)))
    exact ⟨hPrincipal.congr (fun p hp => F05_flatA_chartPrincipal hA (h p.2) i p hp.1),
      fun k => (hDrift k).congr (fun p hp => congrFun (F05_flatB_chartDrift hA (h p.2) i p hp.1) k)⟩
  exact hProduct

end Yau.Proofs.F05Aux
