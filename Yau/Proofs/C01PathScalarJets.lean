import Yau.Proofs.C01PathMetricJets

/-! The actual scalar-curvature derivative along a spatial path and
variable positive time, in the original central-chart directions. -/

noncomputable section

open Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_scalar_along_path_hasDerivAt
    (hflow : LocalizedFlow X o h U P ρ) {x₀ x₁ : Pt X}
    (γ : PiecewiseC1Curve x₀ x₁) (τ : ℝ → ℝ) (s a : ℝ)
    (hγc : ContinuousAt γ.toFun s)
    (hγd : DifferentiableAt ℝ
      (fun u : ℝ => extChartAt (ComplexModel n) (γ s) (γ u)) s)
    (hτ : HasDerivAt τ a s) (ht : 0 < τ s) :
    HasDerivAt (fun u => scalarCurvature (h (τ u)) (γ u))
      (2 * (∑ i, pathChartVelocity γ s i *
        wirt (fun z => Complex.ofReal (inChart (γ s) (scalarCurvature (h (τ s))) z))
          (chartPt (γ s) (γ s)) (stdVec i)).re +
        a * deriv (fun t => scalarCurvature (h t) (γ s)) (τ s)) s := by
  let y := γ s
  let z : ℝ → ComplexVector n := fun u => chartPt y (γ u)
  let F : ComplexVector n × ℝ → ℝ := fun p => scalarCurvature (h p.2) (chartInv y p.1)
  have hz0 : z s = chartPt y y := rfl
  have hz : HasDerivAt z (pathChartVelocity γ s) s := hγd.hasFDerivAt.hasDerivAt
  have hp : (z s, τ s) ∈ chartTarget y ×ˢ Set.Ioi 0 :=
    ⟨mem_extChartAt_target (I := ComplexModel n) y, ht⟩
  have hF : DifferentiableAt ℝ F (z s, τ s) :=
    ((localizedFlow_scalar_spacetime_contDiffOn hflow y).contDiffAt
      (((isOpen_extChartAt_target (I := ComplexModel n) y).prod isOpen_Ioi).mem_nhds hp)).differentiableAt
        (by simp)
  have hc := spacetime_curve_hasDerivAt hF hz hτ
  have hgerm : (fun u => scalarCurvature (h (τ u)) (γ u)) =ᶠ[𝓝 s]
      (fun u => F (z u, τ u)) := by
    have hsource : ∀ᶠ u in 𝓝 s, γ u ∈ (extChartAt (ComplexModel n) y).source :=
      hγc.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) y).mem_nhds
        (mem_extChartAt_source y))
    filter_upwards [hsource] with u hu
    change scalarCurvature (h (τ u)) (γ u) =
      scalarCurvature (h (τ u)) (chartInv y (chartPt y (γ u)))
    change scalarCurvature (h (τ u)) (γ u) = scalarCurvature (h (τ u))
      ((extChartAt (ComplexModel n) y).symm ((extChartAt (ComplexModel n) y) (γ u)))
    rw [(extChartAt (ComplexModel n) y).left_inv hu]
  have hcenter : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  have htime : (fun t => F (chartPt y y, t)) = (fun t => scalarCurvature (h t) y) := by
    funext t
    dsimp only [F]
    rw [hcenter]
  have hderiv :
      2 * (wirt (fun p => (F (p, τ s) : ℂ)) (z s) (pathChartVelocity γ s)).re +
        a * deriv (fun t => F (z s, t)) (τ s) =
      2 * (∑ i, pathChartVelocity γ s i *
        wirt (fun p => Complex.ofReal (inChart y (scalarCurvature (h (τ s))) p))
          (chartPt y y) (stdVec i)).re +
        a * deriv (fun t => scalarCurvature (h t) y) (τ s) := by
    rw [hz0, htime]
    change 2 * (wirt (fun p => Complex.ofReal (inChart y (scalarCurvature (h (τ s))) p))
      (chartPt y y) (pathChartVelocity γ s)).re + _ = _
    rw [wirt_stdVec_sum]
  have hd := hc.congr_of_eventuallyEq hgerm
  rw [hderiv] at hd
  exact hd

end Yau.NodeProofs.C01Aux
