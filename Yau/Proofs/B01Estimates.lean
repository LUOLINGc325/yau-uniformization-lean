import Yau.Proofs.B01Volume
import Yau.Proofs.B01Nakano

open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory Bundle

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

theorem hermitianNormSq_smul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (a : ℂ) (v : V) :
    hermitianNormSq h (a • v) = Complex.normSq a * hermitianNormSq h v := by
  unfold hermitianNormSq
  rw [h.map_smul_left, h.map_smul_right]
  have he : star a * (h.toFun v v * a) = (a * star a) * h.toFun v v := by ring
  rw [he, Complex.star_def, Complex.mul_conj]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem hermitian_square_bound {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : HermitianInnerProduct V) (s u : V) (b : ℂ) (l : ℝ) (hl : 0 < l) :
    2 * (star b * h.toFun s u).re - l * hermitianNormSq h u ≤
      hermitianNormSq h s * ‖b‖ ^ 2 / l := by
  let a : ℂ := b / (l : ℂ)
  have hex : l ^ 2 * hermitianNormSq h (u + (-a) • s) =
      l ^ 2 * hermitianNormSq h u - 2 * l * (star b * h.toFun s u).re +
        Complex.normSq b * hermitianNormSq h s := by
    unfold hermitianNormSq
    rw [h.map_add_left, h.map_add_right, h.map_add_right,
      h.map_smul_right, h.map_smul_left, h.map_smul_left, h.map_smul_right,
      h.conjugate_symmetric u s]
    simp only [a, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
      Complex.neg_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.div_ofReal_re, Complex.div_ofReal_im, h.self_adjoint,
      Complex.normSq_apply]
    field_simp [hl.ne']
    ring
  have hpos := mul_nonneg (sq_nonneg l) (hermitianNormSq_nonneg h (u + (-a) • s))
  rw [hex, Complex.normSq_eq_norm_sq] at hpos
  apply (le_div_iff₀ hl).mpr
  nlinarith

variable {M : ComplexManifold 1} {r : ℕ}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem flatDiscField_topForm_norm (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (k : BundleDbar.Metric E) (s : Section E) (u : BundleDbar.NQForm E 0)
    (hu : IsSectionTopForm E c s u) (x : M.Carrier) :
    BundleDbar.formNormSq (r := r) E (flatDiscField c hc) k u x = hermitianNormSq (k x) (s x) := by
  let A : ℂ := discDerivative c x (chartVec x x (stdVec 0))
  have hval : LeafProofs.L14Aux.topFormValue E u x x = A • s x :=
    hu x Fin.elim0 (fun i => chartVec x x (stdVec i))
  have hdet : (gMat (flatDiscField c hc) x).det.re = Complex.normSq A := by
    have he := flatDiscField_hMat_det c hc x (mem_extChartAt_target x)
    rw [← discDerivative_chartVec c hc x (mem_extChartAt_target x) (stdVec 0)] at he
    have hself : chartInv x (extChartAt (ComplexModel 1) x x) = x :=
      (extChartAt (ComplexModel 1) x).left_inv (mem_extChartAt_source x)
    rw [hself] at he
    change (gMat (flatDiscField c hc) x).det = (Complex.normSq A : ℂ) at he
    exact congrArg Complex.re he
  have hpos : 0 < Complex.normSq A := by
    rw [← hdet]
    exact (Complex.pos_iff.mp (LeafProofs.gMat_posDef (flatDiscField c hc) x).det_pos).1
  rw [LeafProofs.formNormSq_top_factor E, LeafProofs.L14Aux.topCoefficientNormSq_eq_value E,
    hval]
  change (gMat (flatDiscField c hc) x)⁻¹.det.re * hermitianNormSq (k x) (A • s x) = _
  rw [hermitianNormSq_smul, LeafProofs.gMat_inv_det_re, hdet]
  rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

theorem sectionTopFormVolumeTransport : SectionTopFormVolumeTransport (r := r) E := by
  intro c hc g μ k φ hg hμ _ _ _ s u _ hu
  rw [LeafProofs.weightedNormSq_top_metric_independent E g (flatDiscField c hc) μ
    ((2 : ℝ≥0∞) • BundlePresentation.discArea c) hμ (flatDiscField_volume c hc) hg (flatDiscField_smooth c hc)]
  unfold BundleDbar.weightedNormSq
  simp only [flatDiscField_topForm_norm E c hc k s u hu]
  rw [lintegral_smul_measure, smul_eq_mul]

end Yau.Proofs.B01Aux
