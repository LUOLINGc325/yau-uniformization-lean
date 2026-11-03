import Yau.Proofs.D06CircleProductCoefficients

/-! The actual angular weak Leibniz rule for one-dimensional Sobolev functions,
proved by the convolution formula on their fixed Fourier coefficients. -/

noncomputable section
namespace Yau.NodeProofs.D06Aux

def intReflect (n : ℤ) : ℤ ≃ ℤ where
  toFun j := n - j
  invFun j := n - j
  left_inv j := by change n - (n - j) = j; omega
  right_inv j := by change n - (n - j) = j; omega

theorem circle_convolution_summable (f g : CircleL2)
    (hg : Summable (fun j : ℤ => ‖circleCoeff g j‖)) (n : ℤ) :
    Summable (fun j : ℤ => circleCoeff g j * circleCoeff f (n - j)) := by
  apply (hg.mul_right ‖circleCoeff f‖).of_norm_bounded
  intro j
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (p := 2) (by norm_num) (circleCoeff f) (n - j)) (norm_nonneg _)

theorem circleWeakDerivative_product {f g df dg : CircleL2}
    (hf : CircleSobolev 1 f) (hg : CircleSobolev 1 g)
    (hdf : CircleWeakDerivative f df) (hdg : CircleWeakDerivative g dg) :
    CircleWeakDerivative (circleProduct f g) (circleProduct df g + circleProduct dg f) := by
  intro n
  have hG := circleSobolev_one_summable_coeff hg
  have hF := circleSobolev_one_summable_coeff hf
  have hs1 := circle_convolution_summable df g hG n
  have hs2 : Summable (fun j : ℤ => circleCoeff f (n - j) * circleCoeff dg j) := by
    have h := (circle_convolution_summable dg f hF n).comp_injective (intReflect n).injective
    apply h.congr
    intro j
    change circleCoeff f (n - j) * circleCoeff dg (n - (n - j)) = _
    rw [show n - (n - j) = j by omega]
  have hreflect : (∑' j : ℤ, circleCoeff f (n - j) * circleCoeff dg j) =
      ∑' j : ℤ, circleCoeff f j * circleCoeff dg (n - j) := by
    calc
      _ = ∑' j : ℤ, circleCoeff f ((intReflect n) j) * circleCoeff dg (n - (intReflect n) j) := by
        apply tsum_congr
        intro j
        change circleCoeff f (n - j) * circleCoeff dg j =
          circleCoeff f (n - j) * circleCoeff dg (n - (n - j))
        rw [show n - (n - j) = j by omega]
      _ = _ := (intReflect n).tsum_eq (fun j : ℤ => circleCoeff f j * circleCoeff dg (n - j))
  have hcalc : (Complex.I * (n : ℂ)) * circleCoeff (circleProduct f g) n =
      circleCoeff (circleProduct df g) n + circleCoeff (circleProduct dg f) n := by
    rw [circleProduct_coeff f g hg, ← tsum_mul_left]
    calc
      (∑' j : ℤ, (Complex.I * (n : ℂ)) * (circleCoeff g j * circleCoeff f (n - j))) =
          ∑' j : ℤ, (circleCoeff g j * circleCoeff df (n - j) + circleCoeff f (n - j) * circleCoeff dg j) := by
        apply tsum_congr
        intro j
        rw [hdf (n - j), hdg j, Int.cast_sub]
        ring
      _ = (∑' j : ℤ, circleCoeff g j * circleCoeff df (n - j)) +
          ∑' j : ℤ, circleCoeff f (n - j) * circleCoeff dg j := hs1.tsum_add hs2
      _ = _ := by rw [hreflect, circleProduct_coeff df g hg, circleProduct_coeff dg f hf]
  change (fourierBasis (T := 2 * Real.pi)).repr (circleProduct df g + circleProduct dg f) n = _
  rw [map_add]
  exact hcalc.symm

end Yau.NodeProofs.D06Aux
