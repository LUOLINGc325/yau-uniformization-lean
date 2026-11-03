import Yau.Proofs.C02CurvatureGaugeEquation
import Yau.Proofs.C02BilinearJetBound

/-! The actual curvature jets satisfy a triangular ordinary-derivative
estimate: order m+1 uses the differential and connection only through m. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {n : ℕ} {M : ComplexManifold n}

local instance recurrence_end_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance recurrence_end_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance recurrence_one_group : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance recurrence_one_space : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance recurrence_tensor_group (k : ℕ) : NormedAddCommGroup (HomogeneousTensor (ComplexVector n) k) := inferInstance
local instance recurrence_tensor_space (k : ℕ) : NormedSpace ℝ (HomogeneousTensor (ComplexVector n) k) := inferInstance
local instance recurrence_linear_group (k : ℕ) : NormedAddCommGroup (ComplexVector n →L[ℝ] HomogeneousTensor (ComplexVector n) k) := inferInstance
local instance recurrence_linear_space (k : ℕ) : NormedSpace ℝ (ComplexVector n →L[ℝ] HomogeneousTensor (ComplexVector n) k) := inferInstance

theorem normalCurvatureJet_succ_norm_le (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃ₗ[ℂ] TangentVector M p)
    (hU : ∀ u v, (g.form p).toFun (U u) (U v) = ⟪u, v⟫_ℂ) (j m : ℕ) (x : ComplexVector n) :
    ‖iteratedFDeriv ℝ (m + 1) (normalCurvatureJet g p U hU j) x‖ ≤
      binomialJetProduct (fun i => ‖iteratedFDeriv ℝ i (normalCurvatureJet g p U hU (j + 1)) x‖)
        (fun i => ‖iteratedFDeriv ℝ i (normalDifferential g p U hU) x‖) m +
      (4 + j) * binomialJetProduct (fun i => ‖iteratedFDeriv ℝ i (normalCurvatureJet g p U hU j) x‖)
        (fun i => ‖iteratedFDeriv ℝ i (normalConnection g p U hU) x‖) m := by
  let T := normalCurvatureJet g p U hU
  let B := normalDifferential g p U hU
  let A := normalConnection g p U hU
  let H := fun y => tensorHeadOperator (ComplexVector n) (T (j + 1) y) (B y)
  let S := fun s : Fin (4 + j) => fun y =>
    tensorSlotConnectionOperator (ComplexVector n) s (T j y) (A y)
  have hT (k : ℕ) : ContDiff ℝ ∞ (T k) := normalCurvatureJet_smooth g p U hU k
  have hB : ContDiff ℝ ∞ B := normalDifferential_smooth g p U hU
  have hA : ContDiff ℝ ∞ A := normalConnection_smooth g p U hU
  have hH : ContDiff ℝ ∞ H :=
    ((tensorHeadOperator (r := 4 + j) (ComplexVector n)).contDiff.comp (hT (j + 1))).clm_apply hB
  have hS (s : Fin (4 + j)) : ContDiff ℝ ∞ (S s) :=
    ((tensorSlotConnectionOperator (ComplexVector n) s).contDiff.comp (hT j)).clm_apply hA
  have hsum : ContDiff ℝ ∞ (fun y => ∑ s : Fin (4 + j), S s y) :=
    ContDiff.sum (fun s hs => hS s)
  have heq : fderiv ℝ (T j) = fun y => H y + ∑ s : Fin (4 + j), S s y :=
    funext (normalCurvatureJet_fderiv_equation g p U hU j)
  have hHb := norm_iteratedFDeriv_bilinear_le (tensorHeadOperator (r := 4 + j) (ComplexVector n))
    (tensorHeadOperator_norm_le_one (r := 4 + j) (ComplexVector n)) (hT (j + 1)) hB x m
  have hSb (s : Fin (4 + j)) := norm_iteratedFDeriv_bilinear_le
    (tensorSlotConnectionOperator (ComplexVector n) s)
    (tensorSlotConnectionOperator_norm_le_one (ComplexVector n) s) (hT j) hA x m
  calc
    _ = ‖iteratedFDeriv ℝ m (fderiv ℝ (T j)) x‖ := norm_iteratedFDeriv_fderiv.symm
    _ = ‖iteratedFDeriv ℝ m H x + ∑ s : Fin (4 + j), iteratedFDeriv ℝ m (S s) x‖ := by
      rw [heq, fun_iteratedFDeriv_add_apply (hH.contDiffAt.of_le (by simp))
        (hsum.contDiffAt.of_le (by simp)), iteratedFDeriv_fun_sum_apply
        (fun s hs => (hS s).contDiffAt.of_le (by simp))]
    _ ≤ ‖iteratedFDeriv ℝ m H x‖ + ∑ s : Fin (4 + j), ‖iteratedFDeriv ℝ m (S s) x‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ _ := by
      apply add_le_add hHb
      calc
        _ ≤ ∑ s : Fin (4 + j), binomialJetProduct
            (fun i => ‖iteratedFDeriv ℝ i (T j) x‖) (fun i => ‖iteratedFDeriv ℝ i A x‖) m :=
          Finset.sum_le_sum (fun s hs => hSb s)
        _ = _ := by simp [T, A]

end Yau.Blueprint.C02Proof
