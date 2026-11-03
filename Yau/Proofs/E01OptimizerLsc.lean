import Yau.Proofs.E01OptimizerMax
import Yau.Proofs.E01DetValue
import Yau.Proofs.E01EnvelopeScale
import Yau.Proofs.E01EnvelopeTopology

/-! Lower semicontinuity of the exact original ellipsoidLogDet on the complete valid chart/time domain. -/

noncomputable section
open scoped Matrix ComplexOrder
open Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem original_ellipsoidLogDet_lowerSemicontinuous {o : Pt X} {h : Flow X} {U P ρ : STF X}
    (hloc : LocalizedFlow X o h U P ρ) (T : ℝ) (x : Pt X) :
    LowerSemicontinuousOn (fun p : ComplexVector n × ℝ => ellipsoidLogDet X h T x p.1 p.2)
      (chartTarget x ×ˢ Ioo 0 T) := by
  let S : Set (ComplexVector n × ℝ) := chartTarget x ×ˢ Ioo 0 T
  let Q := {p : ComplexVector n × ℝ // p ∈ S}
  let v : Q × ComplexVector n → EReal := fun q => envelopeChart h T x (q.1.val.1, q.2, q.1.val.2)
  have hv : LowerSemicontinuous v := envelopeChart_validParameters_lowerSemicontinuous h T x
  have hhom : ∀ p : Q, ∀ r : ℝ, 0 < r → ∀ η : ComplexVector n,
      v (p, (r : ℂ) • η) = ((r ^ 2 : ℝ) : EReal) * v (p, η) := by
    intro p r hr η
    exact envelopeChart_positive_real_smul h T x p.val.1 η p.val.2 p.property.1 p.property.2 r hr
  have hclip : ∀ p : Q, ∃ C B₀ : Herm n, C.IsHermitian ∧ B₀.PosDef ∧
      (∀ η, v (p, η) ≤ (ellipsoidQuadratic C η : EReal)) ∧
      (∀ η, (ellipsoidQuadratic B₀ η : EReal) ≤ v (p, η)) := by
    intro p
    obtain ⟨hG, hH, hlow, hupp⟩ :=
      envelopeChart_cometric_bounds hloc T x p.val.1 p.val.2 p.property.1 p.property.2
    exact ⟨(hMat (h p.val.2) x p.val.1)⁻¹ᵀ, (hMat X.metric.form x p.val.1)⁻¹ᵀ,
      hH.isHermitian, hG, hupp, hlow⟩
  have hL := lowerSemicontinuous_log_sup_minorant_determinants v hv hhom hclip
  have heq : (fun p : Q => ellipsoidLogDet X h T x p.val.1 p.val.2) =
      (fun p : Q => Real.log (sSup {d : ℝ | ∃ D : Herm n, D.PosDef ∧
        (∀ η, (ellipsoidQuadratic D η : EReal) ≤ v (p, η)) ∧ d = D.det.re})) := by
    funext p
    unfold ellipsoidLogDet
    congr 1
    congr 1
    ext d
    simp only [FeasibleEllipsoid, ellipsoidQuadratic, v, and_assoc]
  have hrestrict : LowerSemicontinuous (fun p : Q => ellipsoidLogDet X h T x p.val.1 p.val.2) := by
    rw [heq]
    exact hL
  exact lowerSemicontinuous_restrict_iff.mp hrestrict

end Yau.NodeProofs.E01Aux
