import Yau.Proofs.F05PhysicalManifoldOperator
import Yau.Proofs.F05FiniteManifoldPatch

/-! Actual chart C2 regularity makes the computed intrinsic operator
linear on finite manifold sums on the original closed domain. -/

open Set
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_intrinsic_operator_finite_sum {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    (T : ℝ) (w : Fin A.count → M.Carrier → ℝ → ℝ)
    (hW : ∀ j i, C2 (F05Q A i T) (pull A i (w j)))
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05IntrinsicLinearOperator c h T (fun x t => ∑ j,w j x t) x t =
      ∑ j,F05IntrinsicLinearOperator c h T (w j) x t := by
  obtain ⟨i,z,hz,heq⟩ := F05_cover hA hx
  rw [← heq]
  let p : Point n := (z,t)
  have hp : p ∈ F05Q A i T := ⟨hz,ht⟩
  have hSum : C2 (F05Q A i T) (pull A i (fun x t => ∑ j,w j x t)) := by
    change C2 (F05Q A i T) (fun p => ∑ j,pull A i (w j) p)
    exact c2_sum Finset.univ (fun j _ => hW j i)
  calc
    _ = linearOp (F05Q A i T) (F05FlowPrincipal A i h c) (F05FlowDrift A i h c)
        (pull A i (fun x t => ∑ j,w j x t)) p :=
      F05_intrinsic_operator_eq_chart hA h c T _ i (p := p) hz (hSum.2.2.2.2.1 p hp)
    _ = ∑ j,linearOp (F05Q A i T) (F05FlowPrincipal A i h c) (F05FlowDrift A i h c)
        (pull A i (w j)) p := linearOp_sum Finset.univ (fun j _ => hW j i) hp
    _ = _ := Finset.sum_congr rfl (fun j _ =>
      (F05_intrinsic_operator_eq_chart hA h c T (w j) i (p := p) hz ((hW j i).2.2.2.2.1 p hp)).symm)

end Yau.Proofs.F05Aux
