import Yau.Proofs.C03CovectorCoordinates

/-! Pulling a source covector back through the same holomorphic inverse
sheet preserves its actual metric normalization and gives a uniform target bound. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.LeafProofs.L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
local instance : ContinuousSMul ℂ (ComplexVector n) where
  continuous_smul := by
    change Continuous (fun p : ℂ × ComplexVector n => WithLp.toLp 2 (fun i => p.1 * p.2 i))
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
      (continuous_pi fun i => continuous_fst.mul
        ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).continuous.comp continuous_snd))

theorem exists_sheet_normalized_covector (O W : Set (ComplexVector n))
    (hO : IsOpen O) (hW : IsOpen W) (h0 : (0 : ComplexVector n) ∈ O)
    (σ θ : ComplexVector n → ComplexVector n) (w0 : ComplexVector n)
    (hw0 : w0 ∈ W) (hσ : ContDiffOn ℂ ∞ σ W) (hθ : ContDiffOn ℂ ∞ θ O)
    (hθ0 : θ 0 = w0) (hστ : ∀ z ∈ O, σ (θ z) = z)
    (Hs Ht : Herm n) (hHt : Ht.PosDef) (U : ℝ) (hU : 0 < U)
    (hupper : HermLE Ht ((U : ℂ) • (1 : Herm n)))
    (hcong : Hs = (linearMatrix (fderiv ℂ θ 0))ᴴ * Ht * linearMatrix (fderiv ℂ θ 0))
    (β : Covector n) (hβunit : dualNormMat Hs (covectorVector β) = 1) :
    ∃ η : Covector n, η.comp (fderiv ℂ θ 0) = β ∧
      dualNormMat Ht (covectorVector η) = 1 ∧ ‖η‖ ≤ Real.sqrt U := by
  let D := fderiv ℂ θ 0
  let E := fderiv ℂ σ w0
  have hσd : DifferentiableAt ℂ σ w0 :=
    (hσ.contDiffAt (hW.mem_nhds hw0)).differentiableAt (by simp)
  have hθd : DifferentiableAt ℂ θ 0 :=
    (hθ.contDiffAt (hO.mem_nhds h0)).differentiableAt (by simp)
  have hfgerm : σ ∘ θ =ᶠ[𝓝 (0 : ComplexVector n)] id := by
    filter_upwards [hO.mem_nhds h0] with z hz
    exact hστ z hz
  have hED : E.comp D = ContinuousLinearMap.id ℂ (ComplexVector n) := by
    have H := fderiv_comp (𝕜 := ℂ) (0 : ComplexVector n)
      (show DifferentiableAt ℂ σ (θ 0) by rw [hθ0]; exact hσd) hθd
    rw [hfgerm.fderiv_eq] at H
    simpa only [D, E, hθ0, fderiv_id] using H.symm
  have hEDv (v : ComplexVector n) : E (D v) = v := congrArg (fun L => L v) hED
  have hDi : Function.Injective D := by
    intro u v huv
    simpa only [hEDv] using congrArg E huv
  have hJ : IsUnit (linearMatrix D).det := isUnit_iff_ne_zero.mpr (linearMatrix_det_ne_zero D hDi)
  let η : Covector n := β.comp E
  have hη : η.comp D = β := by
    ext v
    change β (E (D v)) = β v
    rw [hEDv]
  have hηunit : dualNormMat Ht (covectorVector η) = 1 := by
    rw [← hη, covectorVector_comp, hcong] at hβunit
    rwa [QOne.dualNormMat_pullback_cancel (linearMatrix D) Ht hJ] at hβunit
  exact ⟨η, hη, hηunit, normalized_covector_norm_le η Ht hHt U hU hupper hηunit⟩

end Yau.Proofs.C03Aux
