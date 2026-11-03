import Yau.Proofs.E02RectCalculus

open Matrix Set
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def fullRankRect (n m : ℕ) : Set (Rect n m) := {M | (M*Mᴴ).det ≠ 0}

theorem gram_contDiff (n m : ℕ) : ContDiff ℝ ∞ (fun M : Rect n m => M*Mᴴ) :=
  (rectMulCLM n m n).contDiff.clm_apply (rectAdjointCLM n m).contDiff

theorem isOpen_fullRankRect (n m : ℕ) : IsOpen (fullRankRect n m) :=
  isOpen_ne_fun (gram_contDiff n m).continuous.matrix_det continuous_const

theorem fullRankRect_iff_posDef {n m : ℕ} (M : Rect n m) :
    M ∈ fullRankRect n m ↔ (M*Mᴴ).PosDef :=
  (Matrix.posSemidef_self_mul_conjTranspose M).posDef_iff_det_ne_zero.symm

end Yau.NodeProofs.E02Aux
