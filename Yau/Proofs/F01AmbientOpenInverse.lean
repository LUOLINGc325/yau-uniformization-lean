import Yau.Proofs.F01AmbientOpenChart

/-! The ambient version of the actual open-component chart also has a
genuinely holomorphic inverse, using only the inherited open-subtype atlas. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

theorem ambientOpenChart_symm_mdifferentiableOn
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target) :
    MDifferentiableOn (ComplexModel n) (ComplexModel n)
      (ambientOpenChart M S hS e).symm (ambientOpenChart M S hS e).target := by
  let c := S.openPartialHomeomorphSubtypeCoe hS.nonempty.to_subtype
  have hcTarget : c.target = (S : Set M.Carrier) :=
    S.openPartialHomeomorphSubtypeCoe_target hS.nonempty.to_subtype
  intro y hy
  change y ∈ (e.trans c).target at hy
  have hyS : y ∈ (S : Set M.Carrier) := by
    rw [← hcTarget]
    exact hy.1
  have hyE : c.symm y ∈ e.target := hy.2
  have hgerm : (Subtype.val ∘ c.symm) =ᶠ[𝓝 y] (fun z : M.Carrier => z) := by
    filter_upwards [S.isOpen.mem_nhds hyS] with z hz
    exact c.right_inv (by simpa only [hcTarget] using hz)
  have hcinv : ContMDiffAt (ComplexModel n) (ComplexModel n) ∞ c.symm y :=
    (ContMDiffAt.subtypeVal_comp_iff S c.symm y).mp
      (contMDiffAt_id.congr_of_eventuallyEq hgerm)
  have heinv : MDifferentiableAt (ComplexModel n) (ComplexModel n) e.symm (c.symm y) :=
    (hei _ hyE).mdifferentiableAt (e.open_target.mem_nhds hyE)
  exact (heinv.comp y (hcinv.mdifferentiableAt (by simp))).mdifferentiableWithinAt

end Yau.NodeProofs.F01Aux
