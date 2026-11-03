import Yau.Proofs.C07ChartCurveFamily
import Yau.Proofs.C07ChartBallMaps

/-! Actual bounded families from the base point to every point of a chart ball. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Set Yau.Proofs.D04AtlasGlueAux

variable {n : ℕ} {M : ComplexManifold n}

def integrableCurve_retarget {g : HermitianField M} {o x y : M.Carrier}
    (γ : IntegrableCurve g o x) (hxy : x = y) : IntegrableCurve g o y :=
  ⟨{ γ.1 with finish_eq := γ.1.finish_eq.trans hxy }, γ.2⟩

theorem exists_chartBall_curve_family (g : SmoothMetric M) (o : M.Carrier)
    (B : ChartBall M) :
    ∃ (K : Set M.Carrier) (L : ℝ)
      (γ : ∀ x : B.outer, IntegrableCurve g.form o x)
      (H : C(unitInterval × B.outer, M.Carrier)),
      IsCompact K ∧ 0 ≤ L ∧
      (∀ p, H p = (γ p.2).1 p.1) ∧
      (∀ x, curveLength g.form (γ x).1 ≤ L) ∧
      (∀ x, ∀ u ∈ Icc (0 : ℝ) 1, (γ x).1 u ∈ K) := by
  obtain ⟨K, L, γ, H, hK, hL, hH, hlength, htrace⟩ :=
    exists_chart_curve_family g o (chartBallMap_contMDiff B)
      (show 0 < 2 * B.radius by linarith [B.radius_pos])
      (show 2 * B.radius < 3 * B.radius by linarith [B.radius_pos])
  let q : C(B.outer, Metric.ball (0 : ComplexVector n) (2 * B.radius)) :=
    ⟨fun x => ⟨chartBallCoord B x, chartBallCoord_outer B x.2⟩,
      (continuousOn_iff_continuous_domRestrict.mp
        (chartBallCoord_continuousOn B)).subtype_mk _⟩
  let δ : ∀ x : B.outer, IntegrableCurve g.form o x :=
    fun x => integrableCurve_retarget (γ (q x)) (chartBallMap_coord B x.2)
  let Q : C(unitInterval × B.outer, M.Carrier) :=
    ⟨fun p => H (p.1, q p.2),
      H.continuous.comp (continuous_fst.prodMk (q.continuous.comp continuous_snd))⟩
  exact ⟨K, L, δ, Q, hK, hL, fun p => hH (p.1, q p.2),
    fun x => hlength (q x), fun x => htrace (q x)⟩

end Yau.Proofs.C07Aux
