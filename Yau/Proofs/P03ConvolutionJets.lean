import Yau.Proofs.P03Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open scoped Topology ContDiff Convolution
open MeasureTheory ContinuousMultilinearMap

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]

def scalarConvolution (f : ComplexVector n → ℂ) (k : ComplexVector n → F) :
    ComplexVector n → F := f ⋆[ContinuousLinearMap.lsmul ℝ ℂ, volume] k

theorem scalarConvolution_iteratedFDeriv (f : ComplexVector n → ℂ)
    (k : ComplexVector n → F) (hf : LocallyIntegrable f volume)
    (hk : ContDiff ℝ ∞ k) (hkc : HasCompactSupport k) (j : ℕ) :
    iteratedFDeriv ℝ j (scalarConvolution f k) =
      scalarConvolution f (iteratedFDeriv ℝ j k) := by
  induction j with
  | zero =>
    funext x
    ext m
    have hi := ((hkc.iteratedFDeriv (𝕜 := ℝ) 0).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℂ) hf
      (hk.iteratedFDeriv_right (m := 0) (by simp)).continuous x).integrable
    change Integrable (fun y => f y • iteratedFDeriv ℝ 0 k (x - y)) volume at hi
    rw [iteratedFDeriv_zero_apply]
    change scalarConvolution f k x =
      (∫ y, f y • iteratedFDeriv ℝ 0 k (x - y)) m
    rw [ContinuousMultilinearMap.integral_apply hi]
    rfl
  | succ j ih =>
    funext x
    let L : ℂ →L[ℝ] (ComplexVector n [×j]→L[ℝ] F) →L[ℝ]
        (ComplexVector n [×j]→L[ℝ] F) := ContinuousLinearMap.lsmul ℝ ℂ
    have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ j k) :=
      hk.iteratedFDeriv_right (by simp)
    have hcD := hkc.iteratedFDeriv (𝕜 := ℝ) j
    have hd := hcD.hasFDerivAt_convolution_right L hf (hD.of_le (by simp)) x
    let I := (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (j + 1) => ComplexVector n) F).symm
    rw [iteratedFDeriv_succ_eq_comp_left, ih]
    change I (fderiv ℝ (scalarConvolution f (iteratedFDeriv ℝ j k)) x) = _
    have hdf := hd.fderiv
    change fderiv ℝ (scalarConvolution f (iteratedFDeriv ℝ j k)) x = _ at hdf
    rw [hdf]
    change I (∫ y, L.precompR (ComplexVector n) (f y)
      (fderiv ℝ (iteratedFDeriv ℝ j k) (x - y))) = _
    have hcomm : (∫ y, I (L.precompR (ComplexVector n) (f y)
        (fderiv ℝ (iteratedFDeriv ℝ j k) (x - y)))) =
      I (∫ y, L.precompR (ComplexVector n) (f y)
        (fderiv ℝ (iteratedFDeriv ℝ j k) (x - y))) := by
      convert! ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := volume)
        (E := ComplexVector n →L[ℝ] ComplexVector n [×j]→L[ℝ] F)
        (F := ComplexVector n [×(j + 1)]→L[ℝ] F)
        (by convert! I.toContinuousLinearEquiv)
        (fun y => L.precompR (ComplexVector n) (f y)
          (fderiv ℝ (iteratedFDeriv ℝ j k) (x - y)))
    rw [← hcomm]
    change (∫ y, I (L.precompR (ComplexVector n) (f y)
      (fderiv ℝ (iteratedFDeriv ℝ j k) (x - y)))) =
      ∫ y, f y • iteratedFDeriv ℝ (j + 1) k (x - y)
    apply integral_congr_ae
    filter_upwards with y
    ext m
    rw [iteratedFDeriv_succ_eq_comp_left]
    rfl

end Yau.NodeProofs.P03Aux
