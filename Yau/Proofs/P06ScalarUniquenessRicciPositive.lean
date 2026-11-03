import Yau.Proofs.P06ScalarUniquenessRicciAlgebra
import Yau.Proofs.P06ScalarUniquenessRicciContraction
import Yau.Proofs.P06OrderAlgebra

/-! Nonnegative bisectional curvature implies positivity of the actual
computed Ricci matrix, by its proved inverse metric Chern contraction. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarUniqueness_curvatureContraction_posSemidef
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hs : ∀ i j k l, star (R i j k l) = R j i l k)
    (hpos : ∀ v w : Fin n → ℂ,
      0 ≤ (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * v i * star (v j) * w k * star (w l)).re)
    (hHerm : Matrix.IsHermitian (fun a b => ∑ k, ∑ l, H⁻¹ k l * R b a k l)) :
    Matrix.PosSemidef (fun a b => ∑ k, ∑ l, H⁻¹ k l * R b a k l) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hHerm.im_star_dotProduct_mulVec_self v).symm⟩
  rw [scalarUniqueness_curvatureContraction_quadratic]
  exact matrix_trace_mul_nonneg _ _ hH.inv.posSemidef
    (scalarUniqueness_curvatureDirection_posSemidef R hs hpos v)


theorem ricci_posSemidef_of_nonnegBisectional
    (h : HermitianField M) (hs : MetricSmooth h) (hk : KahlerClosed h)
    (hBC : NonnegBisectional h) : ∀ x, (ricci h x).PosSemidef := by
  intro x
  have heq : ricci h x = (fun a b => ∑ k, ∑ l, (gMat h x)⁻¹ k l * chernCurvature h x b a k l) := by
    ext a b
    exact ricci_eq_chern_contraction h hs hk x a b
  rw [heq]
  apply scalarUniqueness_curvatureContraction_posSemidef (gMat h x)
    (L12Aux.hMat_posDef h x (chartPt x x) (mem_extChartAt_target x))
    (chernCurvature h x)
  · intro i j k l
    exact chernInChart_star h hs x (chartPt x x) (mem_extChartAt_target x) i j k l
  · intro v w
    exact hBC x (WithLp.toLp 2 v) (WithLp.toLp 2 w)
  · rw [← heq]
    exact G04Aux.ricci_hermitian h hs x

/-- The original manifold data already imply the Ricci sign needed by
volume comparison.  No additional geometry assumption is supplied. -/
theorem kahlerManifold_ricci_posSemidef (X : KahlerManifold n) :
    ∀ x, (ricci X.metric.form x).PosSemidef := by
  have hs := L12Aux.metricSmooth_of_smoothMetric X.metric
  have hstrict := (G01Aux.paperPositive_iff_griffithsPositive X.metric.form hs X.kahler_metric).mp
    X.positive_bisectional_curvature
  apply ricci_posSemidef_of_nonnegBisectional X.metric.form hs X.kahler_metric
  intro x v w
  by_cases hv : v = 0
  · subst v
    simp [bisectionalForm]
  · by_cases hw : w = 0
    · subst w
      simp [bisectionalForm]
    · exact (hstrict x v w hv hw).le

end Yau.NodeProofs.P06Aux
