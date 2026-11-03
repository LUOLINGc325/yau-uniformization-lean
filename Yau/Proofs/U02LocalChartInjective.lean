import Yau.Blueprint.Nodes

/-! A genuine local biholomorphic chart is injective in one neighbourhood
of each point, by the ordinary inverse function theorem in its actual chart. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.NodeProofs.U02Proof
open Yau Blueprint

theorem local_injective_of_bijective_manifold_derivative {n : ℕ} {M : ComplexManifold n}
    {Phi : ComplexVector n → M.Carrier} {a : ComplexVector n}
    (hs : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Phi a)
    (hd : Function.Bijective (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi a)) :
    ∃ V ∈ 𝓝 a, Set.InjOn Phi V := by
  let g := (chartPt (Phi a)) ∘ Phi
  have hchart : ContMDiffAt (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞
      (chartPt (Phi a)) (Phi a) := contMDiffAt_extChartAt
  have hg : ContDiffAt ℂ ∞ g a := (hchart.comp a hs).contDiffAt
  have hD : Function.Bijective (fderiv ℂ g a) := by
    have hh := (tangentSpaceCastModel (ComplexModel n) (Phi a)).bijective.comp
      (hd.comp (tangentSpaceCastModel 𝓘(ℂ, ComplexVector n) a).symm.bijective)
    have hm := hs.mdifferentiableAt (by simp)
    have heq : (fun v : ComplexVector n =>
        (tangentSpaceCastModel (ComplexModel n) (Phi a))
          (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi a
            ((tangentSpaceCastModel 𝓘(ℂ, ComplexVector n) a).symm v))) =
        fderiv ℂ g a := by
      funext v
      simp [mfderiv, hm, writtenInExtChartAt, g, chartPt, mfld_simps]
      rfl
    change Function.Bijective (fun v : ComplexVector n =>
      (tangentSpaceCastModel (ComplexModel n) (Phi a))
        (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Phi a
          ((tangentSpaceCastModel 𝓘(ℂ, ComplexVector n) a).symm v))) at hh
    rw [heq] at hh
    exact hh
  let e := (LinearEquiv.ofBijective (fderiv ℂ g a).toLinearMap hD).toContinuousLinearEquiv
  have hge : HasFDerivAt g (e : ComplexVector n →L[ℂ] ComplexVector n) a :=
    hg.differentiableAt (by simp) |>.hasFDerivAt
  let A := hg.toOpenPartialHomeomorph g hge (by simp : (∞ : ℕ∞ω) ≠ 0)
  have ha : a ∈ A.source := hg.mem_toOpenPartialHomeomorph_source hge (by simp)
  refine ⟨A.source, A.open_source.mem_nhds ha, ?_⟩
  intro u hu v hv huv
  apply A.injOn hu hv
  change chartPt (Phi a) (Phi u) = chartPt (Phi a) (Phi v)
  rw [huv]

theorem unitaryChart_local_injective {n : ℕ} {M : ComplexManifold n}
    {h : HermitianField M} {p : M.Carrier} {Phi : ComplexVector n → M.Carrier}
    {r c C : ℝ} (hc : UnitaryChart h p Phi r c C) {a : ComplexVector n}
    (ha : a ∈ Metric.ball 0 r) : ∃ V ∈ 𝓝 a, Set.InjOn Phi V := by
  exact local_injective_of_bijective_manifold_derivative
    ((hc.1.1 a ha).contMDiffAt (Metric.isOpen_ball.mem_nhds ha)) (hc.1.2 a ha)

end Yau.NodeProofs.U02Proof
