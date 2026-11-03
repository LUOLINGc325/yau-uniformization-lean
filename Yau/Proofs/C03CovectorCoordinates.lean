import Yau.Proofs.C03QOneMatrix
import Yau.Proofs.C03LogDualOrder
import Yau.Proofs.C03ChernGaugeJacobian

/-! Actual continuous linear covectors have the expected transpose
coordinate transformation and the genuine Euclidean dual norm. -/

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.Proofs.C03Aux
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.LeafProofs.L17Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def covectorVector (η : Covector n) : ComplexVector n := WithLp.toLp 2 (fun i => η (stdVec i))

theorem covector_apply_sum (η : Covector n) (v : ComplexVector n) :
    η v = ∑ i, v i * η (stdVec i) := by
  have hv : (∑ i, v i • stdVec i) = v := by
    ext j
    simp [stdVec, PiLp.single_apply, Pi.single_apply, Finset.sum_apply', PiLp.smul_apply, eq_comm]
  calc
    η v = η (∑ i, v i • stdVec i) := congrArg η hv.symm
    _ = ∑ i, v i * η (stdVec i) := by simp only [map_sum, map_smul, smul_eq_mul]

theorem covectorVector_norm (η : Covector n) : ‖covectorVector η‖ = ‖η‖ := by
  let e : ComplexVector n := WithLp.toLp 2 (fun i => star (η (stdVec i)))
  have he : η = innerSL ℂ e := by
    ext v
    rw [covector_apply_sum]
    simp only [innerSL_apply_apply, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change v i * η (stdVec i) = inner ℂ (star (η (stdVec i))) (v i)
    simp only [RCLike.inner_apply, starRingEnd_apply, star_star]
  calc
    ‖covectorVector η‖ = ‖e‖ := by
      simp only [covectorVector, e, EuclideanSpace.norm_eq, norm_star]
    _ = ‖η‖ := by rw [he, innerSL_apply_norm]

theorem covectorVector_comp (η : Covector n) (D : ComplexVector n →L[ℂ] ComplexVector n) :
    covectorVector (η.comp D) = matrixFiberMap (linearMatrix D)ᵀ (covectorVector η) := by
  ext j
  change η (D (stdVec j)) = ∑ i, (linearMatrix D) i j * η (stdVec i)
  exact covector_apply_sum η (D (stdVec j))

theorem normalized_covector_norm_le (η : Covector n) (H : Herm n) (hH : H.PosDef)
    (U : ℝ) (hU : 0 < U) (hupper : HermLE H ((U : ℂ) • (1 : Herm n)))
    (hunit : dualNormMat H (covectorVector η) = 1) : ‖η‖ ≤ Real.sqrt U := by
  have hscalar : (((U : ℂ) • (1 : Herm n)) : Herm n).PosDef :=
    (Matrix.PosDef.one : (1 : Herm n).PosDef).smul (Complex.zero_lt_real.mpr hU)
  have hbound := dualNormMat_antitone H ((U : ℂ) • (1 : Herm n)) hH hscalar hupper
    (covectorVector η)
  rw [LogDual.dualNormMat_real_one U hU, covectorVector_norm, hunit] at hbound
  have hs : ‖η‖ ^ 2 ≤ U := by
    have H := (div_le_iff₀ hU).mp hbound
    simpa only [one_mul] using H
  exact (Real.le_sqrt (norm_nonneg η) hU.le).mpr hs

end Yau.Proofs.C03Aux
