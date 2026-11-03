import Yau.Proofs.E01InitialEnvelope
import Yau.Proofs.E01CometricDet
import Yau.Proofs.E01OptimizerUnique

/-! Existence and uniqueness for the original FeasibleEllipsoid definition and its actual sSup. -/

noncomputable section
open scoped Matrix ComplexOrder
open Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint
open Yau.Blueprint.V03Proof

variable {n : ℕ} {X : KahlerManifold n}

theorem envelopeChart_cometric_bounds {o : Pt X} {h : Flow X} {U P ρ : STF X}
    (hloc : LocalizedFlow X o h U P ρ) (T : ℝ) (x : Pt X) (z : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T) :
    ((hMat X.metric.form x z)⁻¹ᵀ).PosDef ∧ ((hMat (h t) x z)⁻¹ᵀ).PosDef ∧
      (∀ η, (ellipsoidQuadratic (hMat X.metric.form x z)⁻¹ᵀ η : EReal) ≤ envelopeChart h T x (z, η, t)) ∧
      (∀ η, envelopeChart h T x (z, η, t) ≤ (ellipsoidQuadratic (hMat (h t) x z)⁻¹ᵀ η : EReal)) := by
  refine ⟨cometric_posDef _ (hMat_posDef X.metric.form x z hz),
    cometric_posDef _ (hMat_posDef (h t) x z hz), ?_, ?_⟩
  · intro η
    exact envelopeChart_actual_initial_lower hloc T x z η t hz ht
  · intro η
    exact envelopeChart_le_actual_dualNormChart h T x z η t hz ht

theorem existsUnique_original_feasible_max {o : Pt X} {h : Flow X} {U P ρ : STF X}
    (hloc : LocalizedFlow X o h U P ρ) (T : ℝ) (x : Pt X) (z : ComplexVector n) (t : ℝ)
    (hz : z ∈ chartTarget x) (ht : t ∈ Ioo 0 T) :
    ∃! B : Herm n, FeasibleEllipsoid X h T x z t B ∧
      ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re := by
  obtain ⟨hG, hH, hlow, hupp⟩ := envelopeChart_cometric_bounds hloc T x z t hz ht
  obtain ⟨B, hB, huniq⟩ := existsUnique_positive_minorant_determinant_max
    (fun η => envelopeChart h T x (z, η, t)) (hMat (h t) x z)⁻¹ᵀ
    (hMat X.metric.form x z)⁻¹ᵀ hH.isHermitian hG hupp hlow
  refine ⟨B, ⟨⟨hB.1, hB.2.1⟩, fun D hD => hB.2.2 D hD.1 hD.2⟩, ?_⟩
  intro D hD
  exact huniq D ⟨hD.1.1, hD.1.2, fun E hE hEv => hD.2 E ⟨hE, hEv⟩⟩

theorem ellipsoidLogDet_eq_logdet_of_original_max
    (h : Flow X) (T : ℝ) (x : Pt X) (z : ComplexVector n) (t : ℝ)
    (B : Herm n) (hB : FeasibleEllipsoid X h T x z t B)
    (hmax : ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re) :
    ellipsoidLogDet X h T x z t = Real.log B.det.re := by
  have hset : {d : ℝ | ∃ D, FeasibleEllipsoid X h T x z t D ∧ d = D.det.re} =
      {d : ℝ | ∃ D : Herm n, D.PosDef ∧
        (∀ η, (ellipsoidQuadratic D η : EReal) ≤ envelopeChart h T x (z, η, t)) ∧ d = D.det.re} := by
    ext d
    simp only [FeasibleEllipsoid, ellipsoidQuadratic, and_assoc]
  unfold ellipsoidLogDet
  rw [hset, sSup_minorant_determinants_eq_max _ B hB.1 hB.2
    (fun D hD hDv => hmax D ⟨hD, hDv⟩)]

end Yau.NodeProofs.E01Aux
