import Yau.Proofs.F05SmoothNearTransport

/-! Actual centered-chart smoothness at every positive space-time point
gives the original all-chart SmoothSpaceTime predicate. This is a genuine
holomorphic chart transition, not an assumed regularity equivalence. -/

open Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smoothNear_spacetime {I : Set ℝ} (W : M.Carrier → ℝ → ℝ)
    (hW : ∀ x t, t ∈ I → SmoothNear W x t) : SmoothSpaceTime W I := by
  intro x p hp
  let y := chartInv x p.1
  let e : OpenPartialHomeomorph (Space n) M.Carrier := (chartAt (Space n) x).symm
  have hInv : (e : Space n → M.Carrier) = chartInv x := by
    funext z
    simp [e,chartInv,ComplexModel]
  have he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source := by
    simpa [e,ComplexModel,extChartAt] using
      (mdifferentiableOn_extChartAt_symm (I := ComplexModel n) (x := x))
  have hMem : p.1 ∈ forwardChartDomain e y := by
    refine ⟨?_,?_⟩
    · simpa [e,chartTarget,ComplexModel,extChartAt] using hp.1
    · rw [hInv]
      exact mem_extChartAt_source y
  have hDomain := (forwardChartDomain_isOpen e y).mem_nhds hMem
  let q : Space n → Space n := fun z => chartPt y (chartInv x z)
  have hQ : ContDiffAt ℝ ∞ q p.1 := by
    have h := (forwardChart_real_contDiffOn e he y).contDiffAt hDomain
    rwa [hInv] at h
  let ψ : Point n → Point n := fun z => (q z.1,z.2)
  have hψ : ContDiffAt ℝ ∞ ψ p :=
    (hQ.comp p contDiffAt_fst).prodMk contDiffAt_snd
  have hY := hW y p.2 hp.2
  change ContDiffAt ℝ ∞ (fun z : Point n => W (chartInv y z.1) z.2) (chartPt y y,p.2) at hY
  have hPoint : ψ p = (chartPt y y,p.2) := rfl
  have hComp : ContDiffAt ℝ ∞ ((fun z : Point n => W (chartInv y z.1) z.2) ∘ ψ) p := by
    apply ContDiffAt.comp _ _ hψ
    rwa [hPoint]
  have hAt : ContDiffAt ℝ ∞ (fun z : Point n => W (chartInv x z.1) z.2) p := by
    apply hComp.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hDomain] with z hz
    change W (chartInv x z.1) z.2 = W (chartInv y (chartPt y (chartInv x z.1))) z.2
    apply congrArg (fun a => W a z.2)
    symm
    apply (extChartAt (ComplexModel n) y).left_inv
    have hSource := hz.2
    rwa [hInv] at hSource
  exact hAt.contDiffWithinAt

end Yau.Proofs.F05Aux
