import Yau.Proofs.E02MatrixBasic
import Yau.Proofs.E02RelativeDet
import Yau.Proofs.V05Matrix

open Matrix
open scoped Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

theorem tracePair_mono_right {n : ℕ} (B K L : Herm n)
    (hB : B.PosSemidef) (hKL : (K-L).PosSemidef) : tracePair B L ≤ tracePair B K := by
  have hh := V05Aux.trace_mul_nonneg hB.transpose hKL
  have hr : 0 ≤ (Matrix.trace (Bᵀ*(K-L))).re := (RCLike.nonneg_iff.mp hh).1
  simpa only [tracePair,Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re,sub_nonneg] using hr

theorem tracePair_mono_left {n : ℕ} (B b K : Herm n)
    (hOrder : (b-B).PosSemidef) (hK : K.PosSemidef) : tracePair B K ≤ tracePair b K := by
  have hh := V05Aux.trace_mul_nonneg hOrder.transpose hK
  have hr : 0 ≤ (Matrix.trace ((b-B)ᵀ*K)).re := (RCLike.nonneg_iff.mp hh).1
  simpa only [tracePair,Matrix.transpose_sub,Matrix.sub_mul,Matrix.trace_sub,
    Complex.sub_re,sub_nonneg] using hr

theorem tracePair_real_smul_left {n : ℕ} (B K : Herm n) (c : ℝ) :
    tracePair ((c : ℂ) • B) K = c*tracePair B K := by
  simp only [tracePair,Matrix.transpose_smul,Matrix.smul_mul,Matrix.trace_smul,
    smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

/-- The relative determinant comparison is applied to the PSD majorant
FIRST. The horizontal lower test matrix may be indefinite. -/
theorem relative_det_trace_majorant {n : ℕ} (B b K L : Herm n)
    (hB : B.PosDef) (hb : b.PosDef) (hOrder : (b-B).PosSemidef)
    (hK : K.PosSemidef) (hDom : (K-L).PosSemidef) :
    (B.det.re/b.det.re)*tracePair b L ≤ tracePair B K := by
  have hBP : 0 < B.det.re := (RCLike.pos_iff.mp hB.det_pos).1
  have hbP : 0 < b.det.re := (RCLike.pos_iff.mp hb.det_pos).1
  have hRatio : 0 ≤ B.det.re/b.det.re := (div_pos hBP hbP).le
  have hRel := posDef_relative_det_order B b hB hb hOrder
  have hUpper := tracePair_mono_left b (((b.det.re/B.det.re : ℝ) : ℂ) • B) K hRel hK
  rw [tracePair_real_smul_left] at hUpper
  calc
    (B.det.re/b.det.re)*tracePair b L ≤ (B.det.re/b.det.re)*tracePair b K :=
      mul_le_mul_of_nonneg_left (tracePair_mono_right b K L hb.posSemidef hDom) hRatio
    _ ≤ (B.det.re/b.det.re)*((b.det.re/B.det.re)*tracePair B K) :=
      mul_le_mul_of_nonneg_left hUpper hRatio
    _ = tracePair B K := by field_simp [hBP.ne',hbP.ne']

end Yau.NodeProofs.E02Aux
