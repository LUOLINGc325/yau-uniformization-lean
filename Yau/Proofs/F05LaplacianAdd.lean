import Yau.Proofs.F05IntrinsicAdd

/-! The literal chart-C2 predicate supplies the actual one-sided time
regularity and linearity of the original scalar Laplacian. -/

open Set
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_time_differentiable {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {T : ℝ} (u : M.Carrier → ℝ → ℝ)
    (hu : ∀ i, C2 (F05Q A i T) (pull A i u))
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    DifferentiableWithinAt ℝ (u x) (Icc 0 T) t := by
  obtain ⟨i,z,hz,heq⟩ := F05_cover hA hx
  rw [← heq]
  have hGiven := (hu i).2.2.2.2.2 (z,t) ⟨hz,ht⟩
  have hFiber : {r | (z,r) ∈ F05Q A i T} = Icc 0 T := by
    ext r
    exact and_iff_right hz
  simpa only [pull,hFiber] using hGiven

theorem F05_laplacian_add_C2 {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (T : ℝ)
    (u v : M.Carrier → ℝ → ℝ)
    (hu : ∀ i, C2 (F05Q A i T) (pull A i u)) (hv : ∀ i, C2 (F05Q A i T) (pull A i v))
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    laplacian (h t) (fun y => u y t+v y t) x =
      laplacian (h t) (fun y => u y t) x+laplacian (h t) (fun y => v y t) x := by
  have hOp := F05_intrinsic_operator_add hA h (fun _ _ => 1) T u v hu hv hx ht
  have hTime := derivWithin_add (F05_time_differentiable hA u hu hx ht) (F05_time_differentiable hA v hv hx ht)
  unfold F05IntrinsicLinearOperator at hOp
  change derivWithin (fun s => u x s+v x s) (Icc 0 T) t = _ at hTime
  dsimp only at hOp
  rw [hTime] at hOp
  linarith

end Yau.Proofs.F05Aux
