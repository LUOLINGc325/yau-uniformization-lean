import Yau.Proofs.F01ChartRescaling

/-! Native differentials of the actual affine chart rescaling. -/
open Set
open scoped Manifold ContDiff
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem rescaleHomeomorph_mfderiv_apply (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0)
    (z v : ComplexVector n) :
    mfderiv (ComplexModel n) (ComplexModel n) (rescaleHomeomorph z₀ a ha) z v = a • v := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℂ (fun w : ComplexVector n => z₀ + a • w) z v = a • v
  have hd : HasFDerivAt (fun w : ComplexVector n => z₀ + a • w)
      (a • ContinuousLinearMap.id ℂ (ComplexVector n)) z := by
    simpa only [id_eq, Pi.smul_apply] using
      ((hasFDerivAt_id (𝕜 := ℂ) z).const_smul a).const_add z₀
  exact DFunLike.congr_fun hd.fderiv v

theorem rescaledChart_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (rescaledChart e z₀ a ha) (rescaledChart e z₀ a ha).source := by
  apply he.comp (rescaleHomeomorph_contDiff z₀ a ha).contMDiff.contMDiffOn
  intro z hz
  exact hz.2

theorem rescaledChart_inverse_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (hei : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target)
    (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (rescaledChart e z₀ a ha).symm (rescaledChart e z₀ a ha).target := by
  apply (rescaleHomeomorph_inverse_contDiff z₀ a ha).contMDiff.comp_contMDiffOn
  apply hei.mono
  intro y hy
  exact hy.1

theorem rescaledChart_mfderiv_apply
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (z₀ : ComplexVector n) (a : ℂ) (ha : a ≠ 0) {z : ComplexVector n}
    (hz : z ∈ (rescaledChart e z₀ a ha).source) (v : ComplexVector n) :
    mfderiv (ComplexModel n) (ComplexModel n) (rescaledChart e z₀ a ha) z v =
      a • mfderiv (ComplexModel n) (ComplexModel n) e (z₀ + a • z) v := by
  have hsource : rescaleHomeomorph z₀ a ha z ∈ e.source := hz.2
  have heAt : MDifferentiableAt (ComplexModel n) (ComplexModel n) e
      (rescaleHomeomorph z₀ a ha z) :=
    ((he _ hsource).contMDiffAt (e.open_source.mem_nhds hsource)).mdifferentiableAt (by simp)
  have haAt := (rescaleHomeomorph_contDiff z₀ a ha).contMDiff.mdifferentiable (by simp) z
  have hv := DFunLike.congr_fun (mfderiv_comp z heAt haAt) v
  change mfderiv (ComplexModel n) (ComplexModel n) (rescaledChart e z₀ a ha) z v =
    mfderiv (ComplexModel n) (ComplexModel n) e (z₀ + a • z)
      (mfderiv (ComplexModel n) (ComplexModel n) (rescaleHomeomorph z₀ a ha) z v) at hv
  apply hv.trans
  rw [rescaleHomeomorph_mfderiv_apply]
  exact (mfderiv (ComplexModel n) (ComplexModel n) e (z₀ + a • z)).map_smul a v

end Yau.NodeProofs.F01Aux
