import Yau.Proofs.C04BoundedGeometryChartsTensorModelDerivative
import Yau.Proofs.C04BoundedGeometryChartsBilinearJetBound

/-! The actual curvature tower has a triangular ordinary-jet bound. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

local instance : NormedAddCommGroup (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance : NormedSpace ℝ (ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance : NormedAddCommGroup (ComplexVector n →L[ℝ] RealTensorForm n r) := inferInstance
local instance : NormedSpace ℝ (ComplexVector n →L[ℝ] RealTensorForm n r) := inferInstance
local instance : NormedAddCommGroup
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance
local instance : NormedSpace ℝ
    (ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) := inferInstance

theorem radialCurvatureForm_triangular_jets
    (g : SmoothMetric M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (m : ℕ) (v : ComplexVector n)
    {K L D H : ℝ} (hK : 0 ≤ K) (hL : 1 ≤ L) (hD : 0 ≤ D) (hH : 1 ≤ H)
    (hscale : (2 : ℝ) ^ m * D * L ≤ H)
    (hzero : ∀ j ≤ m, ‖radialCurvatureForm g p U j v‖ ≤ K)
    (hmodel : ∀ j ≤ m, tensorModelStepNorm n j ≤ D)
    (hA : ∀ l < m, ‖iteratedFDeriv ℝ l (radialCoframe g p U) v‖ ≤ L)
    (hw : ∀ l < m, ‖iteratedFDeriv ℝ l (radialConnection g p U) v‖ ≤ L) :
    ∀ l j, j + l ≤ m →
      ‖iteratedFDeriv ℝ l (radialCurvatureForm g p U j) v‖ ≤ K * H ^ l := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
    intro j hj
    cases l with
    | zero => simpa using hzero j (by omega)
    | succ l =>
      have hlm : l < m := by omega
      have hLp : 0 ≤ L := le_trans zero_le_one hL
      have hHp : 0 ≤ H := le_trans zero_le_one hH
      have hP : 0 ≤ K * H ^ l := mul_nonneg hK (pow_nonneg hHp _)
      have ht (a : ℕ) (ha : a + l ≤ m) :
          ∀ k ≤ l, ‖iteratedFDeriv ℝ k (radialCurvatureForm g p U a) v‖ ≤ K * H ^ l := by
        intro k hk
        exact (ih k (by omega) a (by omega)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hH hk) hK)
      have hAA : ∀ k ≤ l, ‖iteratedFDeriv ℝ k (radialCoframe g p U) v‖ ≤ L :=
        fun k hk => hA k (by omega)
      have hww : ∀ k ≤ l, ‖iteratedFDeriv ℝ k (radialConnection g p U) v‖ ≤ L :=
        fun k hk => hw k (by omega)
      let fI := fun y => tensorInsertionBilinear n (4 + j)
        (radialCurvatureForm g p U (j + 1) y) (radialCoframe g p U y)
      let fC := fun y => tensorConnectionBilinear n (4 + j)
        (radialCurvatureForm g p U j y) (radialConnection g p U y)
      have hI : ContDiff ℝ ∞ fI :=
        ((tensorInsertionBilinear n (4 + j)).contDiff.comp
          (radialCurvatureForm_smooth g p U (j + 1))).clm_apply (radialCoframe_smooth g p U)
      have hC : ContDiff ℝ ∞ fC :=
        ((tensorConnectionBilinear n (4 + j)).contDiff.comp
          (radialCurvatureForm_smooth g p U j)).clm_apply (radialConnection_smooth g p U)
      have hIb : ‖iteratedFDeriv ℝ l fI v‖ ≤
          ‖tensorInsertionBilinear n (4 + j)‖ * 2 ^ l * (K * H ^ l) * L :=
        bilinear_jet_bound_flat _ _ _ (radialCurvatureForm_smooth g p U (j + 1))
          (radialCoframe_smooth g p U) l v hP hLp (ht (j + 1) (by omega)) hAA
      have hCb : ‖iteratedFDeriv ℝ l fC v‖ ≤
          ‖tensorConnectionBilinear n (4 + j)‖ * 2 ^ l * (K * H ^ l) * L :=
        bilinear_jet_bound_flat _ _ _ (radialCurvatureForm_smooth g p U j)
          (radialConnection_smooth g p U) l v hP hLp (ht j (by omega)) hww
      have heq : fderiv ℝ (radialCurvatureForm g p U j) = fI + fC :=
        funext (fun y => radialCurvatureForm_fderiv_eq g p U j y)
      have hc : (2 : ℝ) ^ l * tensorModelStepNorm n j * L ≤ H := by
        calc
          _ ≤ 2 ^ m * D * L := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
                (hmodel j (by omega)) (tensorModelStepNorm_nonneg n j) (by positivity)) hLp
          _ ≤ H := hscale
      calc
        ‖iteratedFDeriv ℝ (l + 1) (radialCurvatureForm g p U j) v‖ =
            ‖iteratedFDeriv ℝ l fI v + iteratedFDeriv ℝ l fC v‖ := by
          rw [← norm_iteratedFDeriv_fderiv, heq,
            iteratedFDeriv_add (hI.of_le (by simp)) (hC.of_le (by simp))]
          rfl
        _ ≤ ‖iteratedFDeriv ℝ l fI v‖ + ‖iteratedFDeriv ℝ l fC v‖ := norm_add_le _ _
        _ ≤ ‖tensorInsertionBilinear n (4 + j)‖ * 2 ^ l * (K * H ^ l) * L +
            ‖tensorConnectionBilinear n (4 + j)‖ * 2 ^ l * (K * H ^ l) * L := add_le_add hIb hCb
        _ = (2 ^ l * tensorModelStepNorm n j * L) * (K * H ^ l) := by
          unfold tensorModelStepNorm
          ring
        _ ≤ H * (K * H ^ l) := mul_le_mul_of_nonneg_right hc hP
        _ = K * H ^ (l + 1) := by rw [pow_succ]; ring

end Yau.Proofs.C04ChartsAux
