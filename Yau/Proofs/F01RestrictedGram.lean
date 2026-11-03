import Yau.Proofs.F01TargetRestriction

/-! The restricted Gram coefficients are computed from the actual inclusion
and its manifold derivative. This transports an ambient chart to the open
submanifold without supplying a free tangent-frame identification. -/
open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology
noncomputable section
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} (M : ComplexManifold n) (S : Opens M.Carrier)
  (hS : IsConnected (S : Set M.Carrier))

def chartGramCoefficient {N : ComplexManifold n} (g : HermitianField N)
    (e : ComplexVector n → N.Carrier) (z : ComplexVector n) (i j : Fin n) : ℂ :=
  (g (e z)).toFun
    (mfderiv (ComplexModel n) (ComplexModel n) e z (stdVec i))
    (mfderiv (ComplexModel n) (ComplexModel n) e z (stdVec j))

def openRestrictedChart
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) :
    OpenPartialHomeomorph (ComplexVector n) (openConnectedManifold M S hS).Carrier :=
  targetRestriction e S hS.nonempty.to_subtype

theorem inclusion_targetRestriction_eventuallyEq
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier) {z : ComplexVector n}
    (hz : z ∈ (openRestrictedChart M S hS e).source) :
    (fun w => openInclusion M S hS (openRestrictedChart M S hS e w)) =ᶠ[𝓝 z] e := by
  filter_upwards [(openRestrictedChart M S hS e).open_source.mem_nhds hz] with w hw
  exact targetRestriction_value e S hS.nonempty.to_subtype hw

theorem inclusion_targetRestriction_mfderiv
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    {z : ComplexVector n} (hz : z ∈ (openRestrictedChart M S hS e).source) :
    (mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS)
      (openRestrictedChart M S hS e z)).comp
      (mfderiv (ComplexModel n) (ComplexModel n) (openRestrictedChart M S hS e) z) =
        mfderiv (ComplexModel n) (ComplexModel n) e z := by
  have hsub : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞
      (openRestrictedChart M S hS e) (openRestrictedChart M S hS e).source :=
    targetRestriction_contMDiffOn e S hS.nonempty.to_subtype he
  have hd := (hsub z hz).contMDiffAt
    ((openRestrictedChart M S hS e).open_source.mem_nhds hz)
  rw [← mfderiv_comp z (openInclusion_mdifferentiable M S hS _)
    (hd.mdifferentiableAt (by simp))]
  exact (inclusion_targetRestriction_eventuallyEq M S hS e hz).mfderiv_eq

theorem openRestrictedField_targetRestriction_coefficient (g : HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : ContMDiffOn (ComplexModel n) (ComplexModel n) ∞ e e.source)
    {z : ComplexVector n} (hz : z ∈ (openRestrictedChart M S hS e).source)
    (i j : Fin n) :
    chartGramCoefficient (openRestrictedField M S hS g)
      (openRestrictedChart M S hS e) z i j =
        chartGramCoefficient g e z i j := by
  have hi := DFunLike.congr_fun (inclusion_targetRestriction_mfderiv M S hS e he hz) (stdVec i)
  have hj := DFunLike.congr_fun (inclusion_targetRestriction_mfderiv M S hS e he hz) (stdVec j)
  change mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS)
    (openRestrictedChart M S hS e z)
    (mfderiv (ComplexModel n) (ComplexModel n) (openRestrictedChart M S hS e) z (stdVec i)) =
      mfderiv (ComplexModel n) (ComplexModel n) e z (stdVec i) at hi
  change mfderiv (ComplexModel n) (ComplexModel n) (openInclusion M S hS)
    (openRestrictedChart M S hS e z)
    (mfderiv (ComplexModel n) (ComplexModel n) (openRestrictedChart M S hS e) z (stdVec j)) =
      mfderiv (ComplexModel n) (ComplexModel n) e z (stdVec j) at hj
  have hx : openInclusion M S hS (openRestrictedChart M S hS e z) = e z :=
    targetRestriction_value e S hS.nonempty.to_subtype hz
  change (g (openInclusion M S hS (openRestrictedChart M S hS e z))).toFun _ _ =
    (g (e z)).toFun _ _
  exact (congrArg₂ (g _).toFun hi hj).trans
    (congrArg (fun x : M.Carrier => (g x).toFun
      (mfderiv (ComplexModel n) (ComplexModel n) e z (stdVec i))
      (mfderiv (ComplexModel n) (ComplexModel n) e z (stdVec j))) hx)

end Yau.NodeProofs.F01Aux
