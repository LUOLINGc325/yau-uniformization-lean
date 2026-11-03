import Yau.Proofs.C03GlobalGeometry
import Yau.LeafProofs.L14

/-! The canonical extended metric has a genuine globally smooth positive
matrix, and its inner-ball matrix is the original displayed pullback. -/

noncomputable section
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs L12Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem gMat_euclidean_field (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn))
    (z : (ComplexEuclideanManifold n hn).Carrier) (a b : Fin n) :
    gMat k z a b = (k z).toFun (stdVec a) (stdVec b) := by
  have hpt : chartPt z z = z := by
    change extChartAt (ComplexModel n) (z : ComplexVector n) z = z
    rw [extChartAt_model_space_eq_id]
    rfl
  rw [gMat, hpt, hMat_euclidean_field]

theorem chartExtendedField_gMat_contDiff (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (a b : Fin n) :
    ContDiff ℝ ∞ (fun z : ComplexVector n =>
      gMat (chartExtendedField hn X Φ r hr hΦ) z a b) := by
  have H := cutoffPullbackField_hMat_contDiff hn X Φ r hΦ
    (chartCutoff n r hr) (fun _ => ⟨ContDiffBump.nonneg _, ContDiffBump.le_one _⟩)
    (chartCutoff n r hr).contDiff (chartCutoff_tsupport_subset r hr)
    (0 : ComplexVector n) a b
  convert H using 1
  funext z
  rw [gMat_euclidean_field, hMat_euclidean_field]
  rfl

theorem chartExtendedField_gMat_posDef (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (z : ComplexVector n) :
    (gMat (chartExtendedField hn X Φ r hr hΦ) z).PosDef :=
  Yau.LeafProofs.gMat_posDef (M := ComplexEuclideanManifold n hn)
    (chartExtendedField hn X Φ r hr hΦ) z

theorem chartExtendedField_gMat_inner (hn : 1 ≤ n) (X : KahlerManifold n)
    (Φ : ComplexVector n → Pt X) (r : ℝ) (hr : 0 < r)
    (hΦ : IsLocalBiholomorphism Φ r) (z : ComplexVector n)
    (hz : z ∈ Metric.closedBall (0 : ComplexVector n) (3 * r / 4)) :
    gMat (chartExtendedField hn X Φ r hr hΦ) z = pullbackMat X.metric.form Φ z := by
  change gMat (cutoffPullbackField hn X Φ r hΦ (chartCutoff n r hr) _) z = _
  rw [cutoffPullbackField_gMat hn X Φ r hΦ _ _ (chartCutoff_tsupport_subset r hr) z,
    (chartCutoff n r hr).one_of_mem_closedBall hz]
  simp only [Complex.ofReal_one, one_smul, sub_self, Complex.ofReal_zero, zero_smul, add_zero]

end Yau.Proofs.C03Aux
