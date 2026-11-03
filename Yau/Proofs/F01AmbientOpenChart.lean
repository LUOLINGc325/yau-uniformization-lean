import Yau.Proofs.F01RestrictedGram
import Yau.LeafProofs.L17ChartNaturality

/-! A chart of the actual open component is an actual ambient partial
homeomorphism after the subtype inclusion; its pulled back metric agrees. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Matrix
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

def ambientOpenChart
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier) :
    OpenPartialHomeomorph (ComplexVector n) M.Carrier :=
  e.trans (S.openPartialHomeomorphSubtypeCoe hS.nonempty.to_subtype)

theorem ambientOpenChart_source
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier) :
    (ambientOpenChart M S hS e).source = e.source := by
  change e.source ∩ e ⁻¹' Set.univ = e.source
  simp only [preimage_univ, inter_univ]

theorem ambientOpenChart_mdifferentiableOn
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source) :
    MDifferentiableOn (ComplexModel n) (ComplexModel n)
      (ambientOpenChart M S hS e) (ambientOpenChart M S hS e).source := by
  intro z hz
  have hze : z ∈ e.source := by simpa only [ambientOpenChart_source] using hz
  exact ((openInclusion_mdifferentiable M S hS (e z)).comp z
    ((he z hze).mdifferentiableAt (e.open_source.mem_nhds hze))).mdifferentiableWithinAt

theorem ambientOpenChart_pullbackMatrix (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    {z : ComplexVector n} (hz : z ∈ e.source) :
    pullbackMatrix (openRestrictedField M S hS g) e z =
      pullbackMatrix g (ambientOpenChart M S hS e) z := by
  have hDe := (he z hz).mdifferentiableAt (e.open_source.mem_nhds hz)
  have hD : (mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS) (e z)).comp
      (mfderiv (ComplexModel n) (ComplexModel n) e z) =
      mfderiv (ComplexModel n) (ComplexModel n) (ambientOpenChart M S hS e) z := by
    rw [← mfderiv_comp z (openInclusion_mdifferentiable M S hS (e z)) hDe]
    rfl
  ext i j
  change (g (e z).val).toFun
    ((mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS) (e z)).comp
      (mfderiv (ComplexModel n) (ComplexModel n) e z) (stdVec i))
    ((mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS) (e z)).comp
      (mfderiv (ComplexModel n) (ComplexModel n) e z) (stdVec j)) = _
  rw [hD]
  rfl

end Yau.NodeProofs.F01Aux
