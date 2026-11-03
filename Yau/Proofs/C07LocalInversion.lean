import Yau.Blueprint.Nodes

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

/-- The derivative condition in the frozen chart definition supplies a
genuine local homeomorphism by the inverse function theorem in one actual
target chart. -/
theorem local_homeomorph_of_localBiholomorphism
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : IsLocalBiholomorphism Φ r) {z : ComplexVector n}
    (hz : z ∈ Metric.ball 0 r) :
    ∃ e : OpenPartialHomeomorph (ComplexVector n) M.Carrier,
      z ∈ e.source ∧ e.source ⊆ Metric.ball 0 r ∧ Set.EqOn e Φ e.source := by
  let a := chartAt (ComplexVector n) (Φ z)
  let g : ComplexVector n → ComplexVector n := fun w => a (Φ w)
  have hΦc : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Φ z :=
    hΦ.1.contMDiffAt (Metric.isOpen_ball.mem_nhds hz)
  have hae : (a : M.Carrier → ComplexVector n) = extChartAt (ComplexModel n) (Φ z) := rfl
  have hac : ContMDiffAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ a (Φ z) := by
    rw [hae]
    exact contMDiffAt_extChartAt
  have hgc : ContDiffAt ℂ ∞ g z := (hac.comp z hΦc).contDiffAt
  have hchain := mfderiv_comp (I := 𝓘(ℂ, ComplexVector n))
    (I' := ComplexModel n) (I'' := 𝓘(ℂ, ComplexVector n)) z
    (hac.mdifferentiableAt (by simp)) (hΦc.mdifferentiableAt (by simp))
  have hai := isInvertible_mfderiv_extChartAt (I := ComplexModel n)
    (x := Φ z) (mem_extChartAt_source (Φ z))
  have haBij : Function.Bijective
      (mfderiv (ComplexModel n) 𝓘(ℂ, ComplexVector n) a (Φ z)) := hai.bijective
  have hgBij : Function.Bijective (fderiv ℂ g z) := by
    have hmg : Function.Bijective
        (mfderiv 𝓘(ℂ, ComplexVector n) 𝓘(ℂ, ComplexVector n) g z) := by
      change Function.Bijective (mfderiv 𝓘(ℂ, ComplexVector n) 𝓘(ℂ, ComplexVector n)
        ((a : M.Carrier → ComplexVector n) ∘ Φ) z)
      rw [hchain]
      exact haBij.comp (hΦ.2 z hz)
    rw [mfderiv_eq_fderiv] at hmg
    have hm : Function.Bijective
        ((NormedSpace.fromTangentSpace (𝕜 := ℂ) (g z)).symm ∘
          (fderiv ℂ g z) ∘ (NormedSpace.fromTangentSpace (𝕜 := ℂ) z)) := hmg
    have hm' := ((NormedSpace.fromTangentSpace (𝕜 := ℂ) (g z)).symm.bijective.of_comp_iff'
      ((fderiv ℂ g z) ∘ (NormedSpace.fromTangentSpace (𝕜 := ℂ) z))).1 hm
    exact (Function.Bijective.of_comp_iff (fderiv ℂ g z)
      (NormedSpace.fromTangentSpace (𝕜 := ℂ) z).bijective).1 hm'
  let D : ComplexVector n ≃L[ℂ] ComplexVector n :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ g z)
      (LinearMap.ker_eq_bot.mpr hgBij.1) (LinearMap.range_eq_top.mpr hgBij.2)
  have hgD : HasFDerivAt g (D : ComplexVector n →L[ℂ] ComplexVector n) z := by
    simpa only [D, ContinuousLinearEquiv.coe_ofBijective] using
      (hgc.differentiableAt (by simp)).hasFDerivAt
  let e₀ := hgc.toOpenPartialHomeomorph g hgD (by simp)
  let U := Metric.ball (0 : ComplexVector n) r ∩ Φ ⁻¹' a.source
  have hU : IsOpen U := hΦ.1.continuousOn.isOpen_inter_preimage Metric.isOpen_ball a.open_source
  let e₁ := e₀.restrOpen U hU
  let e := e₁.trans a.symm
  have hze₀ : z ∈ e₀.source := hgc.mem_toOpenPartialHomeomorph_source hgD (by simp)
  have hza : Φ z ∈ a.source := mem_chart_source (ComplexVector n) (Φ z)
  have hze₁ : z ∈ e₁.source := ⟨hze₀, hz, hza⟩
  have hze : z ∈ e.source := ⟨hze₁, a.map_source hza⟩
  refine ⟨e, hze, ?_, ?_⟩
  · intro w hw
    exact hw.1.2.1
  · intro w hw
    exact a.left_inv hw.1.2.2

end Yau.Proofs.C07Aux
