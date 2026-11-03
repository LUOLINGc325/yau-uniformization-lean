import Yau.Proofs.F01ComplexLeviFrobenius
import Yau.Proofs.F01BackgroundRealificationJets
import Yau.Proofs.F01DilatedCoefficientHolder
import Yau.Proofs.F01MatrixSmooth

/-! The actual complex Frobenius background and Ricci matrices have
uniform jets and the clamped-time Holder budget used in the real principal
coefficient bootstrap. The entry-array and matrix norms are kept explicit. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem background_matrix_frobenius_smooth (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => pullbackMatrix g (A.chart p) z) (ball 0 A.radius) :=
  matrix_contDiffOn_of_entries (A.coefficient_smooth p)

theorem background_matrix_frobenius_uniform_jets (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p z => pullbackMatrix g (A.chart p) z) (fun _ => ball 0 A.radius) :=
  (background_array_uniform_jets A k).comp_clm (fun _ => isOpen_ball)
    (background_array_smooth A) complexArrayToFrobeniusCLM

theorem backgroundRicci_eq_leviSecondMatrix (A : BoundedChartFamily g) (p : M.Carrier)
    {z : Space n} (hz : z ∈ ball 0 A.radius) :
    (-leviSecondMatrixCLM) (backgroundLogDetHessian A p z) =
      backgroundRicci (pullbackMatrix g (A.chart p)) z := by
  have hq : ContDiffAt ℝ 2 (A.backgroundLogDet p) z :=
    ((A.backgroundLogDet_smooth p).contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp)
  rw [neg_apply]
  change -leviSecondMatrixCLM (fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) z) = _
  rw [leviSecondMatrixCLM_eq_native hq]
  rfl

theorem backgroundRicci_frobenius_smooth (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => backgroundRicci (pullbackMatrix g (A.chart p)) z) (ball 0 A.radius) := by
  have h := (-leviSecondMatrixCLM).contDiff.comp_contDiffOn (A.backgroundLogDet_hessian_smooth p)
  apply h.congr
  intro z hz
  exact (backgroundRicci_eq_leviSecondMatrix A p hz).symm

theorem backgroundRicci_frobenius_uniform_jets (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p z => backgroundRicci (pullbackMatrix g (A.chart p)) z)
      (fun _ => ball 0 A.radius) := by
  have h := (A.backgroundLogDet_hessian_uniformJetBounds k).comp_clm
    (fun _ => isOpen_ball) A.backgroundLogDet_hessian_smooth (-leviSecondMatrixCLM)
  apply h.congr (fun _ => isOpen_ball)
  intro p z hz
  exact backgroundRicci_eq_leviSecondMatrix A p hz

theorem complex_background_clamped_holder_budget (A : BoundedChartFamily g) {β : ℝ} (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ A.radius → ρ ≤ 1 → ∀ p : M.Carrier,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun q => pullbackMatrix g (A.chart p) (ρ • q.1) +
          max q.2 0 • (-(ρ ^ 2) • backgroundRicci (pullbackMatrix g (A.chart p)) (ρ • q.1))) K := by
  obtain ⟨K, hK, hk⟩ := dilated_affine_holder_budget
    (background_matrix_frobenius_uniform_jets A 1) (backgroundRicci_frobenius_uniform_jets A 1)
    (background_matrix_frobenius_smooth A) (backgroundRicci_frobenius_smooth A) hβ
  refine ⟨K, hK, ?_⟩
  intro ρ hρ hρr hρ1 p
  apply hk ρ hρ hρr hρ1 (-(ρ ^ 2)) ?_ p
  rw [abs_neg, abs_of_nonneg (sq_nonneg _)]
  nlinarith

end Yau.NodeProofs.F01Aux
