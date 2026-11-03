import Yau.Proofs.C07LocalInversion

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Filter

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual chart representation has the invertible complex derivative
required by the ordinary inverse function theorem. -/
theorem coordinate_chart_invertible {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : IsLocalBiholomorphism Φ r) {z : ComplexVector n} (hz : z ∈ Metric.ball 0 r) :
    ContDiffAt ℂ ∞ (fun w => chartPt (Φ z) (Φ w)) z ∧
      Function.Bijective (fderiv ℂ (fun w => chartPt (Φ z) (Φ w)) z) := by
  let g : ComplexVector n → ComplexVector n := fun w => chartPt (Φ z) (Φ w)
  have hΦc := hΦ.1.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)
  have hac : ContMDiffAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞
      (chartPt (Φ z)) (Φ z) := contMDiffAt_extChartAt
  refine ⟨(hac.comp z hΦc).contDiffAt, ?_⟩
  have hchain := mfderiv_comp (I := 𝓘(ℂ, ComplexVector n))
    (I' := ComplexModel n) (I'' := 𝓘(ℂ, ComplexVector n)) z
    (hac.mdifferentiableAt (by simp)) (hΦc.mdifferentiableAt (by simp))
  have hai := isInvertible_mfderiv_extChartAt (I := ComplexModel n)
    (x := Φ z) (mem_extChartAt_source (Φ z))
  have hmg : Function.Bijective
      (mfderiv 𝓘(ℂ, ComplexVector n) 𝓘(ℂ, ComplexVector n) g z) := by
    change Function.Bijective (mfderiv 𝓘(ℂ, ComplexVector n) 𝓘(ℂ, ComplexVector n)
      ((chartPt (Φ z)) ∘ Φ) z)
    rw [hchain]
    exact hai.bijective.comp (hΦ.2 z hz)
  rw [mfderiv_eq_fderiv] at hmg
  have hm : Function.Bijective
      ((NormedSpace.fromTangentSpace (𝕜 := ℂ) (g z)).symm ∘
        (fderiv ℂ g z) ∘ (NormedSpace.fromTangentSpace (𝕜 := ℂ) z)) := hmg
  have hm' := ((NormedSpace.fromTangentSpace (𝕜 := ℂ) (g z)).symm.bijective.of_comp_iff'
    ((fderiv ℂ g z) ∘ (NormedSpace.fromTangentSpace (𝕜 := ℂ) z))).1 hm
  exact (Function.Bijective.of_comp_iff (fderiv ℂ g z)
    (NormedSpace.fromTangentSpace (𝕜 := ℂ) z).bijective).1 hm'

/-- Every topological inverse branch of the original holomorphic chart is
holomorphic on its actual target. -/
theorem inverse_branch_mdifferentiable {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : IsLocalBiholomorphism Φ r)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hsource : e.source ⊆ Metric.ball 0 r) (heq : Set.EqOn e Φ e.source) :
    MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) e.symm e.target := by
  intro y hy
  let x := e.symm y
  have hx : x ∈ e.source := e.map_target hy
  have hxy : e x = y := e.right_inv hy
  let a := chartAt (ComplexVector n) y
  let d := e.trans a
  let g : ComplexVector n → ComplexVector n := fun w => chartPt (Φ x) (Φ w)
  obtain ⟨hgc, hgBij⟩ := coordinate_chart_invertible hΦ (hsource hx)
  let D : ComplexVector n ≃L[ℂ] ComplexVector n :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ g x)
      (LinearMap.ker_eq_bot.mpr hgBij.1) (LinearMap.range_eq_top.mpr hgBij.2)
  have hgD : HasFDerivAt g (D : ComplexVector n →L[ℂ] ComplexVector n) x := by
    simpa only [D, ContinuousLinearEquiv.coe_ofBijective] using
      (hgc.differentiableAt (by simp)).hasFDerivAt
  have heqg : (d : ComplexVector n → ComplexVector n) =ᶠ[𝓝 x] g := by
    filter_upwards [e.open_source.mem_nhds hx] with w hw
    change a (e w) = chartPt (Φ x) (Φ w)
    rw [heq hw]
    have hΦx : Φ x = y := (heq hx).symm.trans hxy
    rw [hΦx]
    rfl
  have hdD : HasFDerivAt d (D : ComplexVector n →L[ℂ] ComplexVector n) x :=
    hgD.congr_of_eventuallyEq heqg
  have hdt : a y ∈ d.target := by
    refine ⟨a.map_source (mem_chart_source (ComplexVector n) y), ?_⟩
    change a.symm (a y) ∈ e.target
    simpa only [a.left_inv (mem_chart_source (ComplexVector n) y)] using hy
  have hdx : d.symm (a y) = x := by
    change e.symm (a.symm (a y)) = x
    rw [a.left_inv (mem_chart_source (ComplexVector n) y)]
  have hdinv : DifferentiableAt ℂ d.symm (a y) :=
    (d.hasFDerivAt_symm hdt (by simpa only [hdx] using hdD)).differentiableAt
  have hcoord : DifferentiableAt ℂ (e.symm ∘ (extChartAt (ComplexModel n) y).symm)
      (extChartAt (ComplexModel n) y y) := by
    exact hdinv
  have hmd : MDifferentiableWithinAt (ComplexModel n) 𝓘(ℂ, ComplexVector n)
      e.symm Set.univ y := by
    apply DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm
    exact hcoord.differentiableWithinAt
  exact (mdifferentiableWithinAt_univ.mp hmd).mdifferentiableWithinAt

end Yau.Proofs.C07Aux
