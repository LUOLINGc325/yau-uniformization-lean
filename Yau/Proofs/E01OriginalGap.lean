import Yau.Proofs.E01OptimizerMax
import Yau.Proofs.E01LogOrder
import Yau.Proofs.E01FlowRatio

/-! The exact original volume gap is between zero and the same actual rho. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ} {X : KahlerManifold n}

theorem original_volumeGap_bounds {o : Pt X} {h : Flow X} {U P ρ : STF X}
    (hloc : LocalizedFlow X o h U P ρ) (T : ℝ) (x : Pt X) (z : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget x) (ht : t ∈ Set.Ioo 0 T)
    (B : Herm n) (hB : FeasibleEllipsoid X h T x z t B)
    (hmax : ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re) :
    0 ≤ volumeGap X h T x z t ∧ volumeGap X h T x z t ≤ ρ (chartInv x z) t := by
  obtain ⟨hG, hH, hlow, hupp⟩ := envelopeChart_cometric_bounds hloc T x z t hz ht
  have hl : Real.log ((hMat X.metric.form x z)⁻¹ᵀ).det.re ≤ Real.log B.det.re :=
    Real.log_le_log (Complex.pos_iff.mp hG.det_pos).1 (hmax _ ⟨hG, hlow⟩)
  have hu : Real.log B.det.re ≤ Real.log ((hMat (h t) x z)⁻¹ᵀ).det.re :=
    logdet_minorant_le_upper (fun η => envelopeChart h T x (z, η, t))
      (hMat (h t) x z)⁻¹ᵀ B hH hB.1 hupp hB.2
  rw [cometric_logdet_eq_neg_logdet _ (hMat_posDef X.metric.form x z hz)] at hl
  rw [cometric_logdet_eq_neg_logdet _ (hMat_posDef (h t) x z hz)] at hu
  have hr := localized_rho_fixed_chart_ratio hloc x z hz t ht.1.le
  unfold volumeGap
  rw [ellipsoidLogDet_eq_logdet_of_original_max h T x z t B hB hmax, logDet]
  constructor <;> linarith

end Yau.NodeProofs.E01Aux
