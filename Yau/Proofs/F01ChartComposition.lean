import Yau.Proofs.F01AffineChangedChart

/-! Actual composition of holomorphic local charts with a full smooth
inverse on their open targets. -/
noncomputable section
open Set
open scoped Manifold ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem affineChangedChart_zero_source
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (z0 : ComplexVector n) (hz0 : z0 ∈ e.source)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    (0 : ComplexVector n) ∈ (affineChangedChart e z0 A hA).source := by
  refine ⟨Set.mem_univ _, ?_⟩
  change affineCoordinateHomeomorph z0 A hA 0 ∈ e.source
  rw [affineCoordinateHomeomorph_apply, map_zero, add_zero]
  exact hz0

theorem chart_composition_zero_source
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (q : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (he0 : (0 : ComplexVector n) ∈ e.source) (hq0 : (0 : ComplexVector n) ∈ q.source)
    (h0 : q 0 = 0) : (0 : ComplexVector n) ∈ (q.trans e).source := by
  refine ⟨hq0, ?_⟩
  change q 0 ∈ e.source
  rw [h0]
  exact he0

theorem chart_composition_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (q : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    (hq : ContDiffOn ℂ ∞ q q.source) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ (q.trans e) (q.trans e).source := by
  apply he.comp (hq.contMDiffOn.mono (fun _ hz => hz.1))
  intro z hz
  exact hz.2

theorem chart_composition_inverse_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (q : OpenPartialHomeomorph (ComplexVector n) (ComplexVector n))
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target)
    (hq : ContDiffOn ℂ ∞ q.symm q.target) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ (q.trans e).symm (q.trans e).target := by
  apply hq.contMDiffOn.comp (he.mono (fun _ hy => hy.1))
  intro y hy
  exact hy.2

end Yau.NodeProofs.F01Aux
