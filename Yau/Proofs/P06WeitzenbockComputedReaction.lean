import Yau.Proofs.P06WeitzenbockHermitian
import Yau.Proofs.P06WeitzenbockReaction
import Yau.Proofs.P06ScalarUniquenessRicciContraction

noncomputable section
open scoped Matrix ComplexOrder Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau G01Aux Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem computedChern_star (h : HermitianField M) (hs : MetricSmooth h)
    (x : M.Carrier) (i j k l : Fin n) :
    star (chernCurvature h x i j k l) = chernCurvature h x j i l k := by
  simpa only [chernInChart_center] using
    P06Aux.chernInChart_star h hs x (chartPt x x) (mem_extChartAt_target x) i j k l

theorem computedChern_pair (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (i j k l : Fin n) :
    chernCurvature h x i j k l = chernCurvature h x k l i j := by
  simpa only [chernInChart_center] using
    P06Aux.chernInChart_pair_exchange h hs hk x (chartPt x x) (mem_extChartAt_target x) i j k l

theorem computedRicci_eq_curvatureAction (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) :
    ricci h x = finiteCurvatureAction (chernCurvature h x) (gMat h x)⁻¹ := by
  ext a b
  simpa only [finiteCurvatureAction, mul_comm] using P06Aux.ricci_eq_chern_contraction h hs hk x a b

/-- The complete computed curvature reaction, with no additional curvature
symmetry or Ricci-contraction hypothesis. -/
theorem curvatureTwoMatrix_eq_raw_reaction
    (g : SmoothMetric M) (hk : IsKahler g) (A : RealForm M 2) (h11 : RealOneOne A)
    (x : M.Carrier) :
    (fun d e => curvatureTwoComponents g.form A x (chartPt x x) ![d,e]) =
      (-2 : ℝ) • (rawReal (hermitianCurvatureReaction g.form A x) * Yau.LeafProofs.L12Aux.jMatrix n) :=
  curvatureTwoMatrix_eq_raw_reaction_of_symmetries g hk A h11 x
    (computedChern_star g.form (L12Aux.metricSmooth_of_smoothMetric g) x)
    (computedChern_pair g.form (L12Aux.metricSmooth_of_smoothMetric g) hk x)

/-- The actual original Hodge calculator on every nonclosed real (1,1)
input is the actual rough covariant Laplacian plus Q. -/
theorem hodgeTwo_oneOne_eq_rough_add_reaction
    (g : SmoothMetric M) (hk : IsKahler g) (A : RealForm M 2)
    (hA : SmoothRealForm A) (h11 : RealOneOne A) (x : M.Carrier) (I : Fin 2 → RIdx n) :
    hodgeComponents g.form x 2 (formComponents A x) (chartPt x x) I =
      roughTwoComponents g.form A x (chartPt x x) I +
        ((-2 : ℝ) • (rawReal (hermitianCurvatureReaction g.form A x) * L12Aux.jMatrix n)) (I 0) (I 1) := by
  rw [hodgeTwo_eq_rough_add_curvature g.form (L12Aux.metricSmooth_of_smoothMetric g)
    A hA x (z := chartPt x x) (mem_extChartAt_target x)]
  congr 1
  have hI : I = ![I 0,I 1] := by funext i; fin_cases i <;> rfl
  have he := congrArg (fun K : Matrix (RIdx n) (RIdx n) ℝ => K (I 0) (I 1))
    (curvatureTwoMatrix_eq_raw_reaction g hk A h11 x)
  simpa only [← hI] using he

end Yau.NodeProofs.P06Weitzenbock
