import Yau.Proofs.C02LocalInverseFieldDerivative
import Yau.Proofs.C02BilinearJetOnBound
import Yau.Proofs.C02JetProductBounds

/-! The triangular inverse-jet estimate on an actual open domain. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance lij_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance lij_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance lij_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance lij_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance lij_left_group : NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance lij_left_space : NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance lij_right_group : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance lij_right_space : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem actualInverseField_jet_norm_on_le {O : Set E} (hO : IsOpen O)
    {B : E → E →L[ℝ] E} (hB : ContDiffOn ℝ ∞ B O)
    (hInv : ∀ y ∈ O, (B y).IsInvertible) {x : E} (hx : x ∈ O) (m : ℕ) :
    ‖iteratedFDeriv ℝ (m + 1) (fun y => (B y).inverse) x‖ ≤
      binomialJetProduct (binomialJetProduct
        (fun i => ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖)
        (fun i => ‖iteratedFDeriv ℝ (i + 1) B x‖))
        (fun i => ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖) m := by
  let C := fun y => (B y).inverse
  let L := inverseDerivativeLeft E
  let R := inverseDerivativeRight E
  let S0 := fun y => L (C y) (fderiv ℝ B y)
  let S1 := fun y => R (S0 y) (C y)
  have hC : ContDiffOn ℝ ∞ C O := by
    intro y hy
    exact ((hInv y hy).contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).comp_contDiffWithinAt y (hB y hy)
  have hDB : ContDiffOn ℝ ∞ (fderiv ℝ B) O := hB.fderiv_of_isOpen hO (by simp)
  have hS0 : ContDiffOn ℝ ∞ S0 O := (L.contDiff.comp_contDiffOn hC).clm_apply hDB
  have hS1 : ContDiffOn ℝ ∞ S1 O := (R.contDiff.comp_contDiffOn hS0).clm_apply hC
  have heq : fderiv ℝ C =ᶠ[𝓝 x] (fun y => -S1 y) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact actualInverseField_fderiv_operator_at
      (((hB y hy).contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp)) (hInv y hy)
  have h0 (i : ℕ) := norm_iteratedFDeriv_bilinearOn_le L
    (inverseDerivativeLeft_norm_le_one E) hO hC hDB hx i
  have h1 := norm_iteratedFDeriv_bilinearOn_le R
    (inverseDerivativeRight_norm_le_one E) hO hS0 hC hx m
  have hNeg : ‖iteratedFDeriv ℝ m (fun y => -S1 y) x‖ = ‖iteratedFDeriv ℝ m S1 x‖ := by
    change ‖iteratedFDeriv ℝ m (-S1) x‖ = _
    rw [iteratedFDeriv_neg_apply, norm_neg]
  calc
    _ = ‖iteratedFDeriv ℝ m (fderiv ℝ C) x‖ := norm_iteratedFDeriv_fderiv.symm
    _ = ‖iteratedFDeriv ℝ m S1 x‖ := by rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds, hNeg]
    _ ≤ _ := h1.trans (binomialJetProduct_mono m (fun i hi => by
      simpa only [norm_iteratedFDeriv_fderiv] using h0 i) (fun i hi => le_refl _)
      (fun i hi => norm_nonneg _) (fun i hi => norm_nonneg _))

end Yau.Blueprint.C02Proof
