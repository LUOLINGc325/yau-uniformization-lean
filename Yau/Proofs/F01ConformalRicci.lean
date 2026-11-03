import Yau.Proofs.F01ConformalSmooth
import Yau.LeafProofs.L17RicciNaturality

/-! The log determinant and Chern Ricci form of the actual conformal metric.
The original nested Wirtinger operator is retained throughout. -/
noncomputable section
open Set Filter
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem conformalField_logDet (g : HermitianField M) (f : M.Carrier → ℝ)
    (a : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a) :
    logDet (conformalField g f) a z = (n : ℝ) * inChart a f z + logDet g a z := by
  have hpos := LeafProofs.L12Aux.hMat_det_re_pos g a hz
  rw [logDet, conformalField_hMat_det]
  have he : (((Real.exp (f (chartInv a z)) : ℂ) ^ n * (hMat g a z).det)).re =
      Real.exp (f (chartInv a z)) ^ n * (hMat g a z).det.re := by
    simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  rw [he, Real.log_mul (pow_pos (Real.exp_pos _) n).ne' hpos.ne',
    Real.log_pow, Real.log_exp]
  rfl

theorem conformalField_ricci (g : HermitianField M) (hg : MetricSmooth g)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) :
    ricci (conformalField g f) x = ricci g x - (n : ℂ) • levi f x := by
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hnhds : chartTarget x ∈ 𝓝 (chartPt x x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hx
  have hfe : ContDiffAt ℝ 2 (inChart x f) (chartPt x x) :=
    ((hf x).contDiffAt hnhds).of_le (by simp)
  have hge : ContDiffAt ℝ 2 (logDet g x) (chartPt x x) :=
    ((LeafProofs.L17Aux.logDet_contDiffOn_of_metricSmooth g hg x).contDiffAt
      hnhds).of_le (by simp)
  have heq : logDet (conformalField g f) x =ᶠ[𝓝 (chartPt x x)]
      (fun z => (n : ℝ) * inChart x f z + logDet g x z) := by
    filter_upwards [hnhds] with z hz
    exact conformalField_logDet g f x hz
  rw [ricci, LeafProofs.L22Aux.leviC_congr_of_eventuallyEq heq,
    LeafProofs.L17Aux.leviC_add (contDiffAt_const.mul hfe) hge,
    LeafProofs.L17Aux.leviC_const_mul hfe]
  change -((n : ℂ) • levi f x + leviC (logDet g x) (chartPt x x)) = _
  rw [neg_add_rev]
  rfl

end Yau.NodeProofs.F01Aux
