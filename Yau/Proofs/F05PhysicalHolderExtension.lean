import Yau.Proofs.F05FlatRegions
import Yau.LeafProofs.L16HalfSpaceHolderExtension

/-! Arbitrary physical Holder sources, without a lateral zero trace, have a
literal global extension. The initial zero slice is preserved exactly. -/

open Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

def F05PhysicalHolderExtension {n : ℕ} (ν : Option (RIdx n)) (f : Point n → ℝ) : Point n → ℝ :=
  match ν with
  | none => f
  | some j => fun p =>
      halfSpaceOddExtension (-(realVec j)) (halfSpaceZeroTraceResidual (-(realVec j)) f) p+
        f (halfSpaceBoundaryProjection (-(realVec j)) p.1,p.2)

theorem F05PhysicalHolderExtension_eq {n : ℕ} (ν : Option (RIdx n)) (f : Point n → ℝ)
    {p : Point n} (hp : p.1 ∈ closure (F05FlatOpen ν)) : F05PhysicalHolderExtension ν f p = f p := by
  cases ν with
  | none => rfl
  | some j =>
    have hj : realCoord p.1 j ≤ 0 := by
      simpa only [F05FlatOpen_closure,mem_ofPred_eq] using hp
    have hNormal : 0 ≤ inner ℝ (-(realVec j)) p.1 := by
      rw [inner_neg_left,real_inner_comm,real_inner_realVec]
      linarith
    simp only [F05PhysicalHolderExtension,halfSpaceOddExtension,ite_eq_left hNormal,halfSpaceZeroTraceResidual]
    ring

theorem F05PhysicalHolderExtension_holder {n : ℕ} (ν : Option (RIdx n))
    {α C T : ℝ} (hα : 0 < α) {f : Point n → ℝ}
    (hf : HolderBound α (cylinder (closure (F05FlatOpen ν)) 0 T) f C) :
    HolderBound α (cylinder univ 0 T) (F05PhysicalHolderExtension ν f) (5*C) := by
  cases ν with
  | none =>
    have hh : HolderBound α (cylinder univ 0 T) f C := by simpa [F05FlatOpen] using hf
    exact holderBound_mono_const hh (by linarith [hf.1])
  | some j =>
    have he : ‖-(realVec j)‖ = 1 := by simp only [norm_neg,realVec_norm]
    have hSpace : closure (F05FlatOpen (some j)) = {x : Space n | 0 ≤ inner ℝ (-(realVec j)) x} := by
      rw [F05FlatOpen_closure]
      ext x
      simp only [mem_ofPred_eq,inner_neg_left,real_inner_comm,real_inner_realVec,neg_nonneg]
    have hh : HolderBound α ({x : Space n | 0 ≤ inner ℝ (-(realVec j)) x} ×ˢ Icc 0 T) f C := by
      simpa only [cylinder,hSpace] using hf
    have hOdd := holderBound_halfSpace_zero_trace_odd_extension he hα hh
    have hTrace := holderBound_halfSpace_boundary_trace hα.le hh
    simpa only [cylinder,F05PhysicalHolderExtension,show 4*C+C = 5*C by ring] using
      holderBound_add hOdd hTrace

theorem F05PhysicalHolderExtension_initial {n : ℕ} (ν : Option (RIdx n))
    {f : Point n → ℝ} (h0 : ∀ x, f (x,0) = 0) (x : Space n) :
    F05PhysicalHolderExtension ν f (x,0) = 0 := by
  cases ν with
  | none => exact h0 x
  | some j =>
    simp only [F05PhysicalHolderExtension,halfSpaceOddExtension,halfSpaceZeroTraceResidual,
      h0,sub_self,neg_zero,ite_self,add_zero]

end Yau.Proofs.F05Aux
