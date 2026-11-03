import Yau.Proofs.F01ChartComposition
import Yau.Proofs.F01QuadraticJacobian

/-! Germwise transport of actual manifold Gram coefficients through the
explicit quadratic coordinate chart. -/
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem quadratic_chart_pullback_germ (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (he0 : (0 : ComplexVector n) ∈ e.source)
    (B : ComplexVector n →L[ℂ] ComplexVector n →L[ℂ] ComplexVector n)
    (q : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (hq : (q : ComplexVector n → ComplexVector n) = quadraticCoordinate B)
    (hq0 : (0 : ComplexVector n) ∈ q.source)
    (G : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hG : pullbackMatrix g e =ᶠ[𝓝 (0 : ComplexVector n)] G) :
    pullbackMatrix g (q.trans e) =ᶠ[𝓝 (0 : ComplexVector n)]
      (fun z => (quadraticJacobian B z)ᴴ * G (quadraticCoordinate B z) * quadraticJacobian B z) := by
  have hqzero : q 0 = 0 := by rw [hq]; exact quadraticCoordinate_zero B
  have hs : (0 : ComplexVector n) ∈ (q.trans e).source :=
    chart_composition_zero_source e q he0 hq0 hqzero
  have hT : Tendsto (quadraticCoordinate B) (𝓝 0) (𝓝 0) := by
    simpa only [quadraticCoordinate_zero] using (quadraticCoordinate_contDiff B).continuous.tendsto 0
  have hGQ := hG.comp_tendsto hT
  have hfun : (q.trans e : ComplexVector n → M.Carrier) = e ∘ quadraticCoordinate B := by
    change (fun z => e (q z)) = _
    rw [hq]
    rfl
  filter_upwards [(q.trans e).open_source.mem_nhds hs, hGQ] with z hz hGz
  have hpoint : quadraticCoordinate B z ∈ e.source := by
    have hh : q z ∈ e.source := hz.2
    rwa [hq] at hh
  have heAt : MDifferentiableAt (ComplexModel n) (ComplexModel n) e (quadraticCoordinate B z) :=
    ((he _ hpoint).contMDiffAt (e.open_source.mem_nhds hpoint)).mdifferentiableAt (by simp)
  have hp := pullbackMatrix_coordinate_composition g heAt (quadraticCoordinate_contDiff B).contDiffAt
  change pullbackMatrix g (e ∘ quadraticCoordinate B) z =
    (quadraticJacobian B z)ᴴ * pullbackMatrix g e (quadraticCoordinate B z) * quadraticJacobian B z at hp
  rw [hfun]
  exact hp.trans (congrArg (fun H : Matrix (Fin n) (Fin n) ℂ =>
    (quadraticJacobian B z)ᴴ * H * quadraticJacobian B z) hGz)

end Yau.NodeProofs.F01Aux
