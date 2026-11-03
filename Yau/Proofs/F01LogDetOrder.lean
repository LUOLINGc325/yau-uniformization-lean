import Yau.Proofs.F01LogDetCurve
import Yau.Proofs.F01TraceOrder

/-! Hermitian order controls the actual logarithmic determinant ratio.
Monotonicity is derived by differentiating the positive affine matrix path. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem matrix_logdet_monotone {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (hBA : (B - A).PosSemidef) :
    Real.log A.det.re ≤ Real.log B.det.re := by
  let H : ℝ → Matrix (Fin n) (Fin n) ℂ := fun s => A + (s : ℂ) • (B - A)
  have hpos (s : ℝ) (hs : s ∈ Icc 0 1) : (H s).PosDef :=
    hA.add_posSemidef (hBA.smul (Complex.nonneg_iff.mpr ⟨hs.1, by simp⟩))
  have hjet (s : ℝ) (i j : Fin n) :
      HasDerivWithinAt (fun r => H r i j) ((B - A) i j) (Icc 0 1) s := by
    have hreal : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) s := by
      convert (hasDerivAt_id s).ofReal_comp using 1 <;> simp
    have hh := ((hreal.mul_const ((B - A) i j)).const_add (A i j)).hasDerivWithinAt (s := Icc 0 1)
    convert hh using 1 <;> first | rfl | simp
  have hlog (s : ℝ) (hs : s ∈ Icc 0 1) :=
    logdet_curve_hasDerivWithinAt H (B - A) (hjet s) (hpos s hs)
  have hmono : MonotoneOn (fun s => Real.log (H s).det.re) (Icc 0 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun s hs => (hlog s hs).continuousWithinAt)
      (fun s hs => (hlog s (interior_subset hs)).mono interior_subset)
      (fun s hs => traceWith_posSemidef_nonneg (hpos s (interior_subset hs)) hBA)
  have hh := hmono (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) zero_le_one
  simpa [H] using hh

theorem logdet_ratio_upper_of_order {H K : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (hK : K.PosDef) {C : ℝ} (hC : 0 < C)
    (horder : ((C : ℂ) • H - K).PosSemidef) :
    Real.log (K.det.re / H.det.re) ≤ (n : ℝ) * Real.log C := by
  have hmono := matrix_logdet_monotone hK horder
  have hHp := (Complex.pos_iff.mp hH.det_pos).1
  have hKp := (Complex.pos_iff.mp hK.det_pos).1
  have hre : (((C : ℂ) • H).det).re = C ^ n * H.det.re := by
    rw [Matrix.det_smul, Fintype.card_fin]
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  rw [hre, Real.log_mul (pow_pos hC n).ne' hHp.ne', Real.log_pow] at hmono
  rw [Real.log_div hKp.ne' hHp.ne']
  linarith

theorem logdet_ratio_upper_of_exp_order {H K : Matrix (Fin n) (Fin n) ℂ}
    (hH : H.PosDef) (hK : K.PosDef) {B : ℝ}
    (horder : ((Real.exp B : ℂ) • H - K).PosSemidef) :
    Real.log (K.det.re / H.det.re) ≤ (n : ℝ) * B := by
  simpa only [Real.log_exp] using logdet_ratio_upper_of_order hH hK (Real.exp_pos B) horder

end Yau.NodeProofs.F01Aux
