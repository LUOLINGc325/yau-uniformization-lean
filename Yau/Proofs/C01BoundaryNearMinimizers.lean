import Yau.Proofs.C01BoundaryNearPathConfinement

/-! Every precision has a genuine integrable near-minimizer confined
to the larger original compact ball. This supplies the actual input of
the compact minimizing-geodesic theorem. -/

noncomputable section

open MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_boundary_confined_nearMinimizingCurves
    (hflow : LocalizedFlow X o h U P ρ) (a : ℝ) (ha : 0 ≤ a)
    (L : ℝ) (hL : 0 < L) (y : Pt X) (hy : y ∈ initialDistanceSphere X.metric o L)
    (hmin : inducedDistance (h a) o y = exitDistanceProfile X.metric (h a) o L) :
    ∀ ε : ℝ, 0 < ε → ∃ β : IntegrableCurve (h a) o y,
      curveLength (h a) β.1 < inducedDistance (h a) o y + ε ∧
      Set.MapsTo β.1 (Set.Icc (0 : ℝ) 1)
        {x | inducedDistance X.metric.form o x ≤ L + 1} := by
  letI := manifold_realSmooth X.manifold
  have hk := localizedFlow_metricSmooth_nonneg hflow a ha
  obtain ⟨δ, hδ, hconfined⟩ := localizedFlow_boundary_nearPath_confinement hflow a ha L hL y hy hmin
  intro ε hε
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  obtain ⟨f, hf₀, hf₁, hf, _, hlen⟩ := exists_smooth_nearMinimizingPath (h a) hk o y η hη
  let γ : PiecewiseC1Curve o y :=
    { toFun := f
      start_eq := hf₀
      finish_eq := hf₁
      breakpoints := ∅
      breakpoints_mem := by simp
      continuous_on := hf.continuous.continuousOn
      piecewise_c1 := fun t _ => contDiffAt_chart_of_contMDiff hf t }
  have hint : IntegrableOn (curveSpeed (h a) γ) (Set.Icc (0 : ℝ) 1) :=
    Yau.LeafProofs.L23Aux.integrable_curveSpeed_of_contMDiff (h a) hk hf
  refine ⟨⟨γ, hint⟩, ?_, ?_⟩
  · change curveLength (h a) (piecewiseC1Curve_of_contMDiff hf) < _
    exact hlen.trans_le (add_le_add le_rfl (min_le_left ε δ))
  · exact hconfined f hf hf₀ hf₁ (hlen.trans_le (add_le_add le_rfl (min_le_right ε δ)))

end Yau.NodeProofs.C01Aux
