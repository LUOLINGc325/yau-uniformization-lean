import Yau.Proofs.E03GapZero
import Yau.Proofs.E03MatrixRigidity
import Yau.Proofs.E01RawUpper
import Yau.Proofs.V03Envelope

/-! Zero scalar gap identifies the actual maximizer with the actual inverse-transpose cometric. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.E01Aux
variable {n : ℕ} {X : KahlerManifold n}

theorem envelopeChart_le_dualNormChart (h : Flow X) (T : ℝ) (c : Pt X)
    (z η : ComplexVector n) (t : ℝ) (hz : z ∈ chartTarget c) (ht : t ∈ Ioo 0 T) :
    envelopeChart h T c (z, η, t) ≤ (dualNormChart (h t) c z η : EReal) := by
  apply (envelopeChart_le_raw (X := X) h T c (z, η, t) ⟨hz, ht⟩).trans
  have hr := envelopeRaw_le_actual_dualNorm h T (chartInv c z)
    (covectorOfCoords c (chartInv c z) η) t ht.1 ht.2
  have hd := dualNorm_cotangentChartInv (h t) c (z := (z, η)) ⟨hz, mem_univ _⟩
  exact hr.trans_eq (congrArg (fun r : ℝ => (r : EReal)) hd)

theorem envelopeChart_eq_dualNormChart (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (hcomp : EllipsoidComparison X h) (hscalar : ScalarComparison X h ρ)
    (T : ℝ) (hT : 0 < T) (c : Pt X) (z η : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget c) (ht : t ∈ Ioo 0 T) :
    envelopeChart h T c (z, η, t) = (dualNormChart (h t) c z η : EReal) := by
  obtain ⟨B, hB, _⟩ := ((hopt T hT c).2 z t hz ht).1
  let C : Herm n := ((hMat (h t) c z)⁻¹)ᵀ
  have hC : C.PosDef := cometric_posDef _ (hMat_posDef (h t) c z hz)
  have hup : ∀ v, envelopeChart h T c (z, v, t) ≤ (ellipsoidQuadratic C v : EReal) := by
    intro v
    exact envelopeChart_le_dualNormChart h T c z v t hz ht
  have hle := psd_minorant_le_upper (fun v => envelopeChart h T c (z, v, t)) C
    hC.isHermitian hup hB.1.1.posSemidef hB.1.2
  have hL := actual_log_value_eq_of_max h T c z t B hB.1 hB.2
  have hzero := volumeGap_eq_zero o h U P ρ hloc hopt hcomp hscalar T hT c z t hz ht
  have hlog : Real.log B.det.re = Real.log C.det.re := by
    rw [volumeGap, hL] at hzero
    have hc := cometric_logdet_eq_neg_logdet _ (hMat_posDef (h t) c z hz)
    change Real.log C.det.re = -logDet (h t) c z at hc
    linarith
  have hBC := eq_of_posDef_order_logdet_eq B C hB.1.1 hC hle hlog
  apply le_antisymm (hup η)
  rw [← hBC]
  exact hB.1.2 η

theorem envelope_eq_dualNorm (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (hcomp : EllipsoidComparison X h) (hscalar : ScalarComparison X h ρ)
    (T : ℝ) (hT : 0 < T) (x : Pt X) (ξ : Covector n) (t : ℝ)
    (ht : 0 < t) (htT : t < T) : envelope h T x ξ t = (dualNorm (h t) x ξ : EReal) := by
  exact envelopeChart_eq_dualNormChart o h U P ρ hloc hopt hcomp hscalar T hT x
    (chartPt x x) (covectorCoords x x ξ) t
    (mem_extChartAt_target (I := ComplexModel n) x) ⟨ht, htT⟩

theorem envelopeRaw_eq_dualNorm (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (hcomp : EllipsoidComparison X h) (hscalar : ScalarComparison X h ρ)
    (T : ℝ) (hT : 0 < T) (x : Pt X) (ξ : Covector n) (t : ℝ)
    (ht : 0 < t) (htT : t < T) : envelopeRaw h T x ξ t = (dualNorm (h t) x ξ : EReal) := by
  apply le_antisymm (envelopeRaw_le_actual_dualNorm h T x ξ t ht htT)
  rw [← envelope_eq_dualNorm o h U P ρ hloc hopt hcomp hscalar T hT x ξ t ht htT]
  have hr := envelopeChart_le_raw (X := X) h T x
    (chartPt x x, covectorCoords x x ξ, t)
    ⟨mem_extChartAt_target (I := ComplexModel n) x, ht, htT⟩
  have hi : cotangentChartInv x (cotangentChart x (x, ξ)) = (x, ξ) :=
    cotangentChart_left_inv x (mem_extChartAt_source x)
  change envelopeChart h T x (chartPt x x, covectorCoords x x ξ, t) ≤
    envelopeRaw h T (cotangentChartInv x (cotangentChart x (x, ξ))).1
      (cotangentChartInv x (cotangentChart x (x, ξ))).2 t at hr
  simpa only [hi, envelope] using hr

end Yau.NodeProofs.E03Aux
