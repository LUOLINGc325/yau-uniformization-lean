import Yau.Proofs.C02InverseDerivativeOperators
import Yau.Proofs.C02BilinearJetOnBound
import Yau.Proofs.C02JetProductBounds

/-! The genuine inverse field has a triangular jet bound. Order m+1
uses its own jets only through m, and the original field through m+1. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.Blueprint.C02Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance ij_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance ij_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance ij_one_group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance ij_one_space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance ij_left_group : NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance ij_left_space : NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance ij_right_group : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance ij_right_space : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem actualInverseField_jet_norm_le {B : E → E →L[ℝ] E} (hB : ContDiff ℝ ∞ B)
    {x : E} (hx : (B x).IsInvertible) (m : ℕ) :
    ‖iteratedFDeriv ℝ (m + 1) (fun y => (B y).inverse) x‖ ≤
      binomialJetProduct (binomialJetProduct
        (fun i => ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖)
        (fun i => ‖iteratedFDeriv ℝ (i + 1) B x‖))
        (fun i => ‖iteratedFDeriv ℝ i (fun y => (B y).inverse) x‖) m := by
  let C := fun y => (B y).inverse
  let O := {y | (B y).IsInvertible}
  let L := inverseDerivativeLeft E
  let R := inverseDerivativeRight E
  let S0 := fun y => L (C y) (fderiv ℝ B y)
  let S1 := fun y => R (S0 y) (C y)
  have hO : IsOpen O := ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hB.continuous
  have hC : ContDiffOn ℝ ∞ C O := by
    intro y hy
    exact (hy.contDiffAt_map_inverse (𝕜 := ℝ) (n := ∞)).comp_contDiffWithinAt y (hB.contDiffOn y hy)
  have hDB : ContDiff ℝ ∞ (fderiv ℝ B) := hB.fderiv_right (by simp)
  have hS0 : ContDiffOn ℝ ∞ S0 O := (L.contDiff.comp_contDiffOn hC).clm_apply hDB.contDiffOn
  have hS1 : ContDiffOn ℝ ∞ S1 O := (R.contDiff.comp_contDiffOn hS0).clm_apply hC
  have heq : fderiv ℝ C =ᶠ[𝓝 x] (fun y => -S1 y) := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact actualInverseField_fderiv_operator E hB hy
  have h0 (i : ℕ) := norm_iteratedFDeriv_bilinearOn_le L (inverseDerivativeLeft_norm_le_one E) hO hC hDB.contDiffOn hx i
  have h1 := norm_iteratedFDeriv_bilinearOn_le R (inverseDerivativeRight_norm_le_one E) hO hS0 hC hx m
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
