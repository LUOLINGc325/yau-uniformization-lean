import Yau.Proofs.P04CanonicalTensors
import Yau.LeafProofs.L14

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder InnerProductSpace
open Bundle Module

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

private theorem star_mul_self_re (z : ℂ) : (star z*z).re=‖z‖^2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply,Complex.mul_re,Complex.star_def,pow_two]

theorem formNormSq_canonicalToTop (g : HermitianField M)
    (S : CanonicalSection M) (x : M.Carrier) :
    BundleDbar.formNormSq (r := 1) (CanonicalCoefficients M) g flatMetric (canonicalToTop S) x =
      canonicalNormSq g S x := by
  have hz : chartPt x x ∈ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) x := by
    rw [coefficient_localDomain]
    exact mem_extChartAt_target x
  have HH := Yau.LeafProofs.L14Aux.formNormSq_top_inChart
    (CanonicalCoefficients M) g flatMetric (canonicalToTop S) x (chartPt x x) hz
  have hx : chartInv x (chartPt x x)=x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  rw [hx] at HH
  simp only [flat_metricMatrix,Fintype.sum_unique,Matrix.one_apply,ite_true,mul_one] at HH
  have hdefault : (default : Fin 1) = 0 := Subsingleton.elim _ _
  rw [hdefault,coefficient_canonicalToTop,star_mul_self_re] at HH
  exact HH.trans (by simp only [canonicalNormSq,gMat,div_eq_mul_inv,mul_comm])

/-- The norm formula holds in every original chart, including overlaps. -/
theorem canonicalNormSq_inChart (g : HermitianField M)
    (S : CanonicalSection M) (a : M.Carrier) {z : ComplexVector n}
    (hz : z ∈ chartTarget a) :
    inChart a (canonicalNormSq g S) z =
      ‖canonicalCoeff S a z‖^2/(hMat g a z).det.re := by
  have hlocal : z ∈ BundleDbar.localDomain (r := 1) (CanonicalCoefficients M) a := by
    rwa [coefficient_localDomain]
  have HH := Yau.LeafProofs.L14Aux.formNormSq_top_inChart
    (CanonicalCoefficients M) g flatMetric (canonicalToTop S) a z hlocal
  rw [formNormSq_canonicalToTop] at HH
  simp only [flat_metricMatrix,Fintype.sum_unique,Matrix.one_apply,ite_true,mul_one] at HH
  have hdefault : (default : Fin 1) = 0 := Subsingleton.elim _ _
  rw [hdefault,coefficient_canonicalToTop,star_mul_self_re] at HH
  exact HH.trans (by rw [div_eq_mul_inv,mul_comm])

theorem canonicalNormSq_nonneg (g : HermitianField M) (S : CanonicalSection M) (x : M.Carrier) :
    0 ≤ canonicalNormSq g S x := by
  exact div_nonneg (sq_nonneg _) (Complex.pos_iff.mp (Yau.LeafProofs.gMat_posDef g x).det_pos).1.le

end Yau.Proofs.P04Aux
