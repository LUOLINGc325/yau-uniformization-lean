import Yau.Proofs.F01ChartBisectional
import Yau.Proofs.F01CurvatureMatrixJets

/-! Nonnegative native bisectional curvature gives the actual nonpositive
background second-jet term in every genuine holomorphic normal chart. -/
noncomputable section
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem normal_metric_mixed_nonpos (g : HermitianField M) (hg : MetricSmooth g)
    (hcurv : NonnegBisectional g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source)
    (hzero : ∀ a b, fderiv ℝ (fun w => pullbackMatrix g e w a b) z = 0) (i a : Fin n) :
    (wirt (fun w => wirtBar (fun y => pullbackMatrix g e y a a) w (stdVec i))
      z (stdVec i)).re ≤ 0 := by
  have hH (a b : Fin n) : ContDiffOn ℝ ∞ (fun w => pullbackMatrix g e w a b) e.source :=
    pullbackMatrix_entry_contDiffOn g hg e he a b
  have hdet : ∀ w ∈ e.source, (pullbackMatrix g e w).det ≠ 0 := by
    intro w hw
    exact ((pullbackMatrix_posDef g e he hei hw).isUnit.map Matrix.detMonoidHom).ne_zero
  have hnormal := curvatureMatrix_at_zero_first_jet (pullbackMatrix g e) e.open_source
    hH hdet hz hzero i i a a
  have hb := pullback_curvature_diagonal_bisectional g hg e he hei hz i a
  dsimp only at hb
  rw [hnormal, Complex.neg_re] at hb
  have hn := hcurv (e z)
    (WithLp.toLp 2 (fun k => linearMatrix (coordinateDifferential e (e z) z) k a))
    (WithLp.toLp 2 (fun k => linearMatrix (coordinateDifferential e (e z) z) k i))
  linarith

theorem normal_metric_mixed_trace_nonpos (g : HermitianField M) (hg : MetricSmooth g)
    (hcurv : NonnegBisectional g)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source)
    (hzero : ∀ a b, fderiv ℝ (fun w => pullbackMatrix g e w a b) z = 0)
    (values : Fin n → ℝ) (hv : ∀ i, 0 < values i) (a : Fin n) :
    (∑ i, (values i)⁻¹ *
      (wirt (fun w => wirtBar (fun y => pullbackMatrix g e y a a) w (stdVec i))
        z (stdVec i)).re) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (hv i).le)
    (normal_metric_mixed_nonpos g hg hcurv e he hei hz hzero i a)

end Yau.NodeProofs.F01Aux
