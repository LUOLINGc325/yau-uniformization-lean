import Yau.Proofs.D05UniformBivector
import Yau.Proofs.D05OperatorBounds
import Yau.Proofs.D05CompactMatrixBounds
import Yau.Proofs.D05GeneratedBundle

/-! The center and inverse-center estimate for every original normalized
frame. The constants are chosen before the disc and frame. -/

open scoped Manifold Topology ContDiff Matrix
noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau V03Proof

theorem frameBivector_inverse_identity {n : ℕ} (S : CotangentMatrix n) (hS : S.det ≠ 0) :
    S⁻¹ = frameBivector S * Matrix.transpose S * -(canonicalBivector : CotangentMatrix n) := by
  have hinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS)
  have hinvT : Matrix.transpose S⁻¹ * Matrix.transpose S = 1 := by
    rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  symm
  unfold frameBivector
  calc
    _ = S⁻¹ * (canonicalBivector : CotangentMatrix n) *
        (Matrix.transpose S⁻¹ * Matrix.transpose S) * -canonicalBivector := by
      simp only [Matrix.mul_assoc]
    _ = S⁻¹ * ((canonicalBivector : CotangentMatrix n) * -canonicalBivector) := by
      rw [hinvT, Matrix.mul_one, Matrix.mul_assoc]
    _ = S⁻¹ := by
      rw [Matrix.mul_neg, canonicalBivector_square, neg_neg, Matrix.mul_one]

theorem normalizedFrame_uniform_center {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    (K : Set (CotangentPoint M)) (hK : CotangentCompact K)
    (x : M.Carrier) (K₀ : Set (CotangentCoord n))
    (hK₀ : IsCompact K₀) (hK₀T : K₀ ⊆ cotangentTarget x) :
    ∃ C : ℝ, 0 < C ∧ ∀ f E, NormalizedDiscFrame G f E →
      (∀ θ, f (circlePoint θ) ∈ K) → InCotangentChart x (f 0) K₀ →
      rectOpNorm (frameInChart x f E 0) ≤ C ∧
        rectOpNorm ((frameInChart x f E 0)⁻¹) ≤ C := by
  classical
  obtain ⟨B, hB, hBE⟩ := normalizedFrame_uniform_bivector hG K hK
  let A : CotangentCoord n → Matrix (Fin q) (CotangentIndex n) ℂ :=
    fun z => cotangentDG G x (cotangentChartInv x z)
  obtain ⟨γ, Γ, hγ, _, hA⟩ := compact_matrix_bounds hK₀
    (fun a j => (cotangentDG_chart_entry_contDiffOn hG.1 x a j).continuousOn.mono hK₀T)
    (fun z hz => toEuclideanLin_injective_of_mulVec (A z)
      (cotangentDG_mulVec_injective_in_chart hG x (cotangentChartInv x z)
        (cotangentChartInv_mapsTo x (hK₀T hz))))
  let C : ℝ := 1 + γ⁻¹ + B * γ⁻¹
  have hγinv : 0 ≤ γ⁻¹ := inv_nonneg.mpr hγ.le
  have hprod : 0 ≤ B * γ⁻¹ := mul_nonneg hB.le hγinv
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f E hE hboundary hcenter
  let S := frameInChart x f E 0
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 1 := by simp
  have hS : rectOpNorm S ≤ γ⁻¹ := by
    unfold rectOpNorm
    apply ContinuousLinearMap.opNorm_le_bound _ hγinv
    intro v
    change ‖Matrix.toEuclideanLin S v‖ ≤ γ⁻¹ * ‖v‖
    have hlo := (hA (cotangentChart x (f 0)) hcenter.2
      (Matrix.toEuclideanLin S v)).1
    rw [cotangentChart_left_inv x hcenter.1] at hlo
    have hu : ‖Matrix.toEuclideanLin (ambientFrame G f E 0) v‖ ≤ ‖v‖ :=
      matrix_closedDisc_norm_le_of_boundary (ambientFrame_entry_contDiffOn hE.1 hG.1)
        hE.2.1 hzero v
    have hcomp : Matrix.toEuclideanLin (cotangentDG G x (f 0))
        (Matrix.toEuclideanLin S v) = Matrix.toEuclideanLin (ambientFrame G f E 0) v := by
      rw [ambientFrame_in_fixed_chart hG.1 f E x 0 hcenter.1]
      exact (LinearMap.congr_fun (Matrix.toLpLin_mul 2 2 2 (cotangentDG G x (f 0)) S) v).symm
    rw [hcomp] at hlo
    have hle : γ * ‖Matrix.toEuclideanLin S v‖ ≤ ‖v‖ := hlo.trans hu
    exact (le_inv_mul_iff₀ hγ).mpr hle
  have hFrob : matrixFrobSq (frameBivector (E 0)) ≤ B ^ 2 :=
    hBE f E hE hboundary 0 hzero
  have hBop : rectOpNorm (frameBivector (E 0)) ≤ B :=
    rectOpNorm_le_of_frobSq _ hB.le hFrob
  have hST : rectOpNorm (Matrix.transpose S) ≤ γ⁻¹ :=
    (rectOpNorm_transpose_le S).trans hS
  have hSinv : rectOpNorm S⁻¹ ≤ B * γ⁻¹ := by
    have hid := frameBivector_inverse_identity S (frameInChart_det_ne_zero hE.1 hzero x hcenter.1)
    rw [frameBivector_in_fixed_chart x f E 0 hcenter.1] at hid
    rw [hid]
    calc
      _ ≤ rectOpNorm (frameBivector (E 0) * Matrix.transpose S) *
          rectOpNorm (-(canonicalBivector : CotangentMatrix n)) := rectOpNorm_mul_le _ _
      _ ≤ (rectOpNorm (frameBivector (E 0)) * rectOpNorm (Matrix.transpose S)) *
          rectOpNorm (-(canonicalBivector : CotangentMatrix n)) :=
        mul_le_mul_of_nonneg_right (rectOpNorm_mul_le _ _) (norm_nonneg _)
      _ ≤ (B * γ⁻¹) * 1 := mul_le_mul
        (mul_le_mul hBop hST (norm_nonneg _) hB.le)
        (rectOpNorm_negative_canonical_le_one n) (norm_nonneg _) hprod
      _ = B * γ⁻¹ := mul_one _
  constructor
  · exact hS.trans (by dsimp only [C]; linarith)
  · exact hSinv.trans (by dsimp only [C]; linarith)

end Yau.Blueprint.D05Proof
