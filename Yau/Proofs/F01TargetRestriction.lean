import Yau.Proofs.F01OpenRestriction

/-! Restrict an actual local parametrization to an open target subtype. Its
map and inverse are fixed by the partial homeomorphism, with no chosen frame. -/
open Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def targetRestriction (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (S : Opens M.Carrier) (hs : Nonempty S) : OpenPartialHomeomorph (ComplexVector n) S :=
  (e.symm.subtypeRestr hs).symm

theorem targetRestriction_source_subset (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (S : Opens M.Carrier) (hs : Nonempty S) : (targetRestriction e S hs).source ⊆ e.source :=
  e.symm.subtypeRestr_target_subset hs

theorem mem_targetRestriction_source (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (S : Opens M.Carrier) (hs : Nonempty S) {z : ComplexVector n}
    (hz : z ∈ e.source) (hSz : e z ∈ S) : z ∈ (targetRestriction e S hs).source := by
  have h := e.symm.map_subtype_source (hs := hs) (x := (⟨e z, hSz⟩ : S)) (e.map_source hz)
  have hEq : e.symm (e z) = z := e.left_inv hz
  change z ∈ (e.symm.subtypeRestr hs).target
  simpa only [hEq] using h

theorem targetRestriction_value (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (S : Opens M.Carrier) (hs : Nonempty S) {z : ComplexVector n}
    (hz : z ∈ (targetRestriction e S hs).source) :
    (targetRestriction e S hs z).val = e z :=
  e.symm.subtypeRestr_symm_apply hs hz

theorem targetRestriction_inverse_value
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (S : Opens M.Carrier) (hs : Nonempty S) (y : S) :
    (targetRestriction e S hs).symm y = e.symm y.val := rfl

theorem targetRestriction_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (S : Opens M.Carrier) (hs : Nonempty S)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (targetRestriction e S hs) (targetRestriction e S hs).source := by
  intro z hz
  have hze := targetRestriction_source_subset e S hs hz
  have hEq : (fun w => (targetRestriction e S hs w).val) =ᶠ[𝓝 z] e :=
    Filter.eventuallyEq_of_mem ((targetRestriction e S hs).open_source.mem_nhds hz)
      (fun w hw => targetRestriction_value e S hs hw)
  have hcomp := ((he z hze).contMDiffAt (e.open_source.mem_nhds hze)).congr_of_eventuallyEq hEq
  exact ((ContMDiffAt.subtypeVal_comp_iff S (targetRestriction e S hs) z).mp hcomp).contMDiffWithinAt

theorem targetRestriction_inverse_contMDiffOn
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (S : Opens M.Carrier) (hs : Nonempty S)
    (hei : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e.symm e.target) :
    ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (targetRestriction e S hs).symm (targetRestriction e S hs).target := by
  intro y hy
  have hye : y.val ∈ e.target := by
    simpa only [targetRestriction, OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.subtypeRestr_source, OpenPartialHomeomorph.symm_source,
      mem_preimage] using hy
  have h := ((hei y.val hye).contMDiffAt (e.open_target.mem_nhds hye)).comp y
    (contMDiff_subtype_val (I := ComplexModel n) (n := ∞) (U := S) y)
  exact h.contMDiffWithinAt

end Yau.NodeProofs.F01Aux
