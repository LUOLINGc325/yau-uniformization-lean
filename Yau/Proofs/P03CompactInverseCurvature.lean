import Yau.Proofs.P03CompactRelativeLevi
import Yau.Proofs.P03RealMetricLeviMatrix
import Yau.Proofs.P03CurvatureCoercivity
import Yau.Proofs.P03InverseCurvatureCoercivity

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs Yau.LeafProofs.L12Aux Yau.LeafProofs.L22Aux

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- A fixed compact source set has one actual inverse-curvature bound for
all weights whose computed Levi forms dominate the same strictly psh ψ. -/
theorem exists_compact_inverseCurvature_bound (g : Yau.SmoothMetric M)
    (h : Metric (M := M) E) (hN : NakanoNonnegative (r := r) E h)
    (ψ : M.Carrier → ℝ) (hψ : IsSmoothStrictPsh ψ) (φ : ℕ → M.Carrier → ℝ)
    (hφ : ∀ j, SmoothFn (φ j))
    (hdom : ∀ j x (v : ComplexVector n),
      complexLeviQuadratic (inChart x ψ) (chartPt x x) v ≤
        complexLeviQuadratic (inChart x (φ j)) (chartPt x x) v)
    (f : NQForm E 1) {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ j : ℕ, ∀ x ∈ K,
      inverseCurvatureNormSq (r := r) E g.form h (φ j) f x ≤
        ENNReal.ofReal (lam⁻¹ * BundleDbar.formNormSq (r := r) E g.form h f x) := by
  obtain ⟨lam, hlam, hlower⟩ := exists_compact_manifold_relative_levi_lower g ψ hψ hK
  refine ⟨lam, hlam, ?_⟩
  intro j x hx
  have hf : ContDiffAt ℝ 2 (inChart x (φ j)) (chartPt x x) :=
    (((hφ j) x).contDiffAt ((isOpen_extChartAt_target x).mem_nhds
      (mem_extChartAt_target x))).of_le (by simp)
  have hLG : (leviC (inChart x (φ j)) (chartPt x x) - (lam : ℂ) • gMat g.form x).PosSemidef :=
    leviC_sub_base_metric_posSemidef g.form x (mem_extChartAt_target x) hf lam hlam.le
      (fun v => (hlower x hx v).trans (hdom j x v))
  exact inverseCurvatureNormSq_le_of_coercive E g.form h (φ j) f x lam hlam
    (fun V => curvatureEnergy_coercive_of_levi E g.form h hN (φ j) x lam hLG V)

end Yau.NodeProofs.P03Aux
