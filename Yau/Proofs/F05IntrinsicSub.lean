import Yau.Proofs.F05PhysicalManifoldOperator
import Yau.LeafProofs.L16ExpBoundaryCalculus

/-! Subtraction preserves the original computed intrinsic operator on C2 data. -/

open Set
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_intrinsic_operator_sub {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    (T : ℝ) (u v : M.Carrier → ℝ → ℝ)
    (hu : ∀ i, C2 (F05Q A i T) (pull A i u)) (hv : ∀ i, C2 (F05Q A i T) (pull A i v))
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05IntrinsicLinearOperator c h T (fun x t => u x t-v x t) x t =
      F05IntrinsicLinearOperator c h T u x t-F05IntrinsicLinearOperator c h T v x t := by
  obtain ⟨i,z,hz,heq⟩ := F05_cover hA hx
  rw [← heq]
  have hp : (z,t) ∈ F05Q A i T := ⟨hz,ht⟩
  have hSub : C2 (F05Q A i T) (pull A i (fun x t => u x t-v x t)) := c2_sub (hu i) (hv i)
  have hSubEq := F05_intrinsic_operator_eq_chart hA h c T (fun x t => u x t-v x t) i
    (p := (z,t)) hz (hSub.2.2.2.2.1 (z,t) hp)
  have huEq := F05_intrinsic_operator_eq_chart hA h c T u i (p := (z,t)) hz ((hu i).2.2.2.2.1 (z,t) hp)
  have hvEq := F05_intrinsic_operator_eq_chart hA h c T v i (p := (z,t)) hz ((hv i).2.2.2.2.1 (z,t) hp)
  rw [hSubEq,huEq,hvEq]
  exact Yau.LeafProofs.L16ExpBoundaryAux.linearOp_sub_at
    ((hu i).2.2.2.2.1 (z,t) hp) ((hv i).2.2.2.2.1 (z,t) hp)
    ((hu i).2.2.2.2.2 (z,t) hp) ((hv i).2.2.2.2.2 (z,t) hp)

end Yau.Proofs.F05Aux
