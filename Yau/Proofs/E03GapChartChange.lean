import Yau.Proofs.E03CenteredTransport
import Yau.Proofs.E03MaxTransport
import Yau.Proofs.E01OptimizerExistence
import Yau.Proofs.E01CometricDet
import Yau.LeafProofs.L17ChartNaturality

/-! SOURCE-ONLY E03 candidate: the actual maximizer and cometric have the same determinant factor. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.E01Aux

variable {n : ℕ} {X : KahlerManifold n}

theorem actual_log_value_eq_of_max (h : Flow X) (T : ℝ) (c : Pt X)
    (z : ComplexVector n) (t : ℝ) (B : Herm n)
    (hB : FeasibleEllipsoid X h T c z t B)
    (hmax : ∀ D, FeasibleEllipsoid X h T c z t D → D.det.re ≤ B.det.re) :
    ellipsoidLogDet X h T c z t = Real.log B.det.re := by
  have hs := sSup_minorant_determinants_eq_max
    (fun η => envelopeChart h T c (z, η, t)) B hB.1 hB.2
    (fun D hD hDv => hmax D ⟨hD, hDv⟩)
  have hset : {d : ℝ | ∃ D, FeasibleEllipsoid X h T c z t D ∧ d = D.det.re} =
      {d : ℝ | ∃ D : Herm n, D.PosDef ∧
        (∀ η, (ellipsoidQuadratic D η : EReal) ≤ envelopeChart h T c (z, η, t)) ∧
        d = D.det.re} := by
    ext d
    simp only [FeasibleEllipsoid, ellipsoidQuadratic, and_assoc]
  unfold ellipsoidLogDet
  rw [hset, hs]

theorem relative_logdet_congruence (B C S : Herm n) (hB : B.PosDef) (hC : C.PosDef)
    (hS : IsUnit S) :
    Real.log (Sᴴ * C * S).det.re - Real.log (Sᴴ * B * S).det.re =
      Real.log C.det.re - Real.log B.det.re := by
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hS
  have hB' := hB.conjTranspose_mul_mul_same hi
  have hC' := hC.conjTranspose_mul_mul_same hi
  have hr := Yau.LeafProofs.L17Aux.determinant_ratio_congruence B C S
    (hS.map Matrix.detMonoidHom).ne_zero
  have hh := congrArg Real.log hr
  rw [Real.log_div (Complex.pos_iff.mp hB'.det_pos).1.ne'
      (Complex.pos_iff.mp hC'.det_pos).1.ne',
    Real.log_div (Complex.pos_iff.mp hB.det_pos).1.ne'
      (Complex.pos_iff.mp hC.det_pos).1.ne'] at hh
  linarith

theorem volumeGap_eq_centered (h : Flow X) (ρ : STF X)
    (hopt : OptimizerContacts X h ρ) (T : ℝ) (hT : 0 < T)
    (c y : Pt X) (hy : y ∈ (extChartAt (ComplexModel n) c).source)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    volumeGap X h T c (chartPt c y) t = volumeGap X h T y (chartPt y y) t := by
  have hz : chartPt c y ∈ chartTarget c := (extChartAt (ComplexModel n) c).map_source hy
  obtain ⟨B, hB, _⟩ := ((hopt T hT c).2 (chartPt c y) t hz ht).1
  let S : Herm n := (tangentFrameMatrix c y y)ᵀ
  let B' : Herm n := Sᴴ * B * S
  let C : Herm n := ((hMat (h t) c (chartPt c y))⁻¹)ᵀ
  have hS : IsUnit S := centered_fiber_matrix_isUnit c y hy
  have htr := determinant_maximum_congruence
    (fun η => envelopeChart h T c (chartPt c y, η, t)) B S hB.1.1 hS hB.1.2
    (fun D hD hDv => hB.2 D ⟨hD, hDv⟩)
  have hB' : FeasibleEllipsoid X h T y (chartPt y y) t B' := by
    refine ⟨htr.1, ?_⟩
    intro η
    simpa only [B', S, ellipsoidQuadratic,
      centered_envelope_congruence h T c y hy η t ht] using htr.2.1 η
  have hmax' : ∀ D, FeasibleEllipsoid X h T y (chartPt y y) t D → D.det.re ≤ B'.det.re := by
    intro D hD
    apply htr.2.2 D hD.1
    intro η
    rw [centered_envelope_congruence h T c y hy η t ht]
    exact hD.2 η
  have hL := actual_log_value_eq_of_max h T c (chartPt c y) t B hB.1 hB.2
  have hL' := actual_log_value_eq_of_max h T y (chartPt y y) t B' hB' hmax'
  have hC : C.PosDef := cometric_posDef _ (hMat_posDef (h t) c (chartPt c y) hz)
  have hrel := relative_logdet_congruence B C S hB.1.1 hC hS
  have hcom : Sᴴ * C * S = ((gMat (h t) y)⁻¹)ᵀ :=
    centered_cometric_congruence (h t) c y hy
  rw [hcom] at hrel
  unfold volumeGap
  rw [hL, hL']
  unfold logDet
  rw [← cometric_logdet_eq_neg_logdet _ (hMat_posDef (h t) c (chartPt c y) hz),
    ← cometric_logdet_eq_neg_logdet _ (hMat_posDef (h t) y (chartPt y y)
      (mem_extChartAt_target (I := ComplexModel n) y))]
  exact hrel.symm

end Yau.NodeProofs.E03Aux
