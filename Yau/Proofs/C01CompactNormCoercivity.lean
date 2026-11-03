import Yau.Proofs.C01CompactMetricCoercivity

/-! The compact positive matrix bound is the actual lower bound for
real tangent speeds used to confine near-minimizing curves. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_compact_speed_lower_bound
    (hflow : LocalizedFlow X o h U P ρ) (a : ℝ) (ha : 0 ≤ a)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ x ∈ K, ∀ v : TangentVector X.manifold x,
      ell ^ 2 * (2 * hermitianNormSq (X.metric.form x) v) ≤
        2 * hermitianNormSq (h a x) v := by
  obtain ⟨c, hc, hb⟩ := localizedFlow_compact_metric_coercivity hflow a ha K hK
  refine ⟨Real.sqrt c, Real.sqrt_pos.mpr hc, ?_⟩
  intro x hx v
  let u : ComplexVector n := tangentSpaceCastModel (ComplexModel n) x v
  have hchart : chartVec x x u = v := by
    rw [Yau.LeafProofs.L12Aux.chartVec_self]
    exact (tangentSpaceCastModel (ComplexModel n) x).symm_apply_apply v
  have hq (k : HermitianField X.manifold) :
      matrixQuadraticReal (gMat k x) u = hermitianNormSq (k x) v := by
    simpa only [matrixQuadraticReal, hchart] using center_metric_quadratic_eq_normSq k x u
  have hv := hb x hx u
  rw [hq X.metric.form, hq (h a)] at hv
  rw [Real.sq_sqrt hc.le]
  linarith

end Yau.NodeProofs.C01Aux
