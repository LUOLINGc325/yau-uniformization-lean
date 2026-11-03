import Yau.Proofs.F03DirichletEnergy
import Yau.LeafProofs.L19SmoothDensity

/-! Genuine uniform supported-core approximation on the actual real manifold. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.F03Aux
open Yau LeafProofs.L12Aux LeafProofs.L19Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem exists_uniform_dirichletCore_approx (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O : Set M.Carrier) {f : M.Carrier → ℝ} (hf : Continuous f)
    (hcf : HasCompactSupport f) (hfo : tsupport f ⊆ O) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : dirichletCore g μ hμ O, ∀ x, |f x-k.val x| < ε := by
  letI := manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := manifold_locallyCompact M
  obtain ⟨k,happrox,hsupport⟩ := hf.exists_contMDiff_approx
    𝓘(ℝ, ComplexVector n) ⊤ (ε := fun _ => ε) continuous_const (fun _ => hε)
  let kd : ScalarEnergyDomain g μ hμ :=
    ⟨k,smoothFn_of_contMDiff_real k k.contMDiff,hcf.mono hsupport⟩
  have hko : kd ∈ dirichletCore g μ hμ O := (closure_mono hsupport).trans hfo
  refine ⟨⟨kd,hko⟩,?_⟩
  intro x
  simpa only [Real.dist_eq,abs_sub_comm] using happrox x

end Yau.Proofs.F03Aux
