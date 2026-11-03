import Yau.Proofs.C02TensorMetricDual
import Yau.Proofs.C02TensorSlotConnection
import Yau.Proofs.C02BilinearJetBound
import Yau.Proofs.C02JetProductBounds

/-! All derivatives of the actual connection curvature obey the exact
double binomial product estimate. Its two highest differential terms
therefore have coefficient one each. -/

noncomputable section
open scoped Manifold InnerProductSpace ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
local instance fj_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance fj_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance fj_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fj_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fj_two_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fj_two_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

local instance fj_tensor_group : NormedAddCommGroup (HomogeneousTensor E 4) := inferInstance
local instance fj_tensor_space : NormedSpace ℝ (HomogeneousTensor E 4) := inferInstance
local instance fj_insert_group : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] HomogeneousTensor E 4) := inferInstance
local instance fj_insert_space : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] HomogeneousTensor E 4) := inferInstance

theorem tensorCurvature_jet_norm_le (T : E → HomogeneousTensor E 4) (B : E → E →L[ℝ] E)
    (hT : ContDiff ℝ ∞ T) (hB : ContDiff ℝ ∞ B) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => tensorMetricDualFour E
      (tensorSlotOperatorAll E (1 : Fin 4) (tensorSlotOperatorAll E (0 : Fin 4) (T y) (B y)) (B y))) x‖ ≤
      binomialJetProduct (binomialJetProduct
        (fun i => ‖iteratedFDeriv ℝ i T x‖) (fun i => ‖iteratedFDeriv ℝ i B x‖))
        (fun i => ‖iteratedFDeriv ℝ i B x‖) m := by
  let L0 := tensorSlotOperatorAll E (0 : Fin 4)
  let L1 := tensorSlotOperatorAll E (1 : Fin 4)
  let D := tensorMetricDualFour E
  let S0 := fun y => L0 (T y) (B y)
  let S1 := fun y => L1 (S0 y) (B y)
  have hS0 : ContDiff ℝ ∞ S0 := (L0.contDiff.comp hT).clm_apply hB
  have hS1 : ContDiff ℝ ∞ S1 := (L1.contDiff.comp hS0).clm_apply hB
  have hD := D.norm_iteratedFDeriv_comp_left (f := S1) (x := x) (n := m) hS1.contDiffAt (show (m : ℕ∞ω) ≤ ∞ by simp)
  have hD1 : ‖D‖ ≤ 1 := tensorMetricDualFour_norm_le_one E
  have hL0 : ‖L0‖ ≤ 1 := tensorSlotOperatorAll_norm_le_one E (0 : Fin 4)
  have hL1 : ‖L1‖ ≤ 1 := tensorSlotOperatorAll_norm_le_one E (1 : Fin 4)
  have h0 (i : ℕ) := norm_iteratedFDeriv_bilinear_le L0 hL0 hT hB x i
  have h1 := norm_iteratedFDeriv_bilinear_le L1 hL1 hS0 hB x m
  change ‖iteratedFDeriv ℝ m (D ∘ S1) x‖ ≤ _
  calc
    _ ≤ ‖iteratedFDeriv ℝ m S1 x‖ := hD.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD1 (norm_nonneg _))
    _ ≤ _ := h1.trans (binomialJetProduct_mono m (fun i hi => h0 i) (fun i hi => le_refl _)
      (fun i hi => norm_nonneg _) (fun i hi => norm_nonneg _))

end Yau.Blueprint.C02Proof
