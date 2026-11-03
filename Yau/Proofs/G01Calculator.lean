import Yau.Blueprint.NormalizationTargets
import Yau.LeafProofs.L14
import Yau.LeafProofs.L17ChartNaturality

noncomputable section
open scoped Manifold Topology ContDiff Matrix
namespace Yau.NodeProofs.G01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

/-- The two central Gram calculators use the same actual chart frame. -/
theorem metricMatrix_eq_gMat (h : HermitianField M) (x : M.Carrier) :
    metricMatrix h x = gMat h x := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  ext i j
  change coordinateCoefficientInChart h x x i j =
    coordinateCoefficientInChart h x (chartInv x (chartPt x x)) i j
  exact congrArg (fun y => coordinateCoefficientInChart h x y i j) hx.symm


/-- Real smoothness suffices to identify Basic's and Calculus's Chern tensors. -/
theorem chernCalculatorCompatibility (h : HermitianField M) (hs : MetricSmooth h) :
    Blueprint.ChernCalculatorCompatibility h := by
  intro x i j k l
  have hf : ContDiffAt ℝ 2 (fun z => hMat h x z j i) (chartPt x x) :=
    ((L17Aux.hMat_contDiffOn_of_metricSmooth h hs x j i).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
        (mem_extChartAt_target x))).of_le (by simp)
  have hm := L14Aux.wirt_wirtBar_comm (fun z => hMat h x z j i)
    (chartPt x x) hf (stdVec l) (stdVec k)
  unfold curvatureComponent chernCurvature
  rw [inverseMetricMatrix, metricMatrix_eq_gMat]
  have hc (a b : Fin n) : chartCoefficientFunction h x a b =
      fun z => hMat h x z a b := by
    funext z
    exact (L12Aux.hMat_eq_chartCoefficientFunction h x z a b).symm
  simp only [coordinateSecondDerivative, coordinateDerivative, coordinateBarDerivative,
    hc, holomorphicCoordinateDerivativeAt, antiholomorphicCoordinateDerivativeAt,
    realCoordinateDerivativeAt, realImaginaryCoordinateDerivativeAt,
    wirt, wirtBar, stdVec, chartPt] at hm ⊢
  rw [hm]

end Yau.NodeProofs.G01Aux
