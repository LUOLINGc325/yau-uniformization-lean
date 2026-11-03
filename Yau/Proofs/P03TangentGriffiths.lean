import Yau.Proofs.P03TangentCurvatureOverlap
import Yau.Proofs.P03GriffithsPullback
import Yau.Proofs.G01BisectionalNormalization

open scoped Manifold Topology ContDiff ComplexOrder Matrix
open Yau.LeafProofs

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n : ℕ} {M : ComplexManifold n}

theorem tangent_curvature_center (g : Yau.SmoothMetric M) (x : M.Carrier)
    (i j α β : Fin n) :
    curvatureMatrix (hMat g.form x) (chartPt x x) i j α β =
      chernCurvature g.form x β α i j := by
  have hc := Yau.NodeProofs.G01Aux.chernF_lower g.form (L12Aux.metricSmooth_of_smoothMetric g) x
    (chartPt x x) (mem_extChartAt_target x) β α i j
  calc
    _ = (hMat g.form x (chartPt x x) *
        Yau.NodeProofs.G01Aux.chernF g.form x (chartPt x x) i j) α β := by
      simp only [curvatureMatrix, Yau.NodeProofs.G01Aux.chernF,
        Yau.NodeProofs.G01Aux.chernA, Yau.NodeProofs.G01Aux.matrixWirtBar,
        Matrix.mul_neg]
      rfl
    _ = Yau.NodeProofs.G01Aux.chernInChart g.form x (chartPt x x) β α i j := hc
    _ = _ := Yau.NodeProofs.G01Aux.chernInChart_center g.form x β α i j

theorem tangent_griffiths_center_eq (g : Yau.SmoothMetric M) (x : M.Carrier)
    (ξ v : ComplexVector n) :
    griffithsQuadratic (curvatureMatrix (hMat g.form x) (chartPt x x)) ξ v =
      bisectionalForm g.form x v ξ := by
  simp only [griffithsQuadratic, tangent_curvature_center, bisectionalForm]
  apply congrArg Complex.re
  calc
    _ = ∑ α, ∑ β, ∑ i, ∑ j,
        chernCurvature g.form x β α i j * ξ i * star (ξ j) * star (v α) * v β :=
      sum_four_swap _
    _ = ∑ β, ∑ α, ∑ i, ∑ j,
        chernCurvature g.form x β α i j * ξ i * star (ξ j) * star (v α) * v β := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro β _
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem tangent_griffiths_center_nonnegative (X : KahlerManifold n)
    (x : X.manifold.Carrier) (ξ v : ComplexVector n) :
    0 ≤ griffithsQuadratic (curvatureMatrix (hMat X.metric.form x) (chartPt x x)) ξ v := by
  rw [tangent_griffiths_center_eq]
  by_cases hv : v = 0
  · subst v
    simp [bisectionalForm]
  by_cases hξ : ξ = 0
  · subst ξ
    simp [bisectionalForm]
  exact (Yau.NodeProofs.G01Aux.paperPositive_iff_griffithsPositive X.metric.form
    (L12Aux.metricSmooth_of_smoothMetric X.metric) X.kahler_metric).mp X.positive_bisectional_curvature x v ξ hv hξ |>.le

/-- The original paper curvature positivity supplies Griffiths
nonnegativity of the computed tangent matrix in every original chart. -/
theorem tangent_griffiths_nonnegative (X : KahlerManifold n)
    (a : X.manifold.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (ξ v : ComplexVector n) :
    0 ≤ griffithsQuadratic (curvatureMatrix (hMat X.metric.form a) z) ξ v := by
  let x := chartInv a z
  let D : Matrix (Fin n) (Fin n) ℂ := fun p i =>
    fderiv ℂ (fun w => chartPt x (chartInv a w)) z (stdVec i) p
  let A := determinantTransitionMatrix a x x
  have hO : z ∈ tangentChartOverlap x a := ⟨hz, mem_extChartAt_source x⟩
  have hR : curvatureMatrix (hMat X.metric.form a) z = fun i j =>
      Aᴴ * (∑ p, ∑ q, (D p i * star (D q j)) •
        curvatureMatrix (hMat X.metric.form x) (chartPt x x) p q) * A := by
    funext i j
    exact tangent_curvature_overlap X.metric x a hO i j
  rw [hR, L07Aux.griffithsQuadratic_conjugate, griffithsQuadratic_base_pullback]
  exact tangent_griffiths_center_nonnegative X x _ _

end Yau.NodeProofs.P03Aux
