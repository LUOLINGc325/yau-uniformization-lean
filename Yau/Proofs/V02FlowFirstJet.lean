import Yau.Proofs.V02FlowNativeComposition

/-! Exact single-column time jets from total single-time slice identities. -/

open scoped Manifold Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n b : ℕ} {M : ComplexManifold n}

theorem finiteFlowCompose_first_time_jet
    (Φ : Fin b → ℂ × NativeCotangentPoint M → NativeCotangentPoint M)
    (hzero : ∀ k y, Φ k (0, y) = y)
    (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ)
    {U : Set (NativeCotangentPoint M)} {R : ℝ} (hU : IsOpen U) (hR : 0 < R)
    (hΨ : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ))
      𝓘(ℂ, CotangentCoord n) ∞ (finiteFlowCompose b Φ) (U ×ˢ ball 0 R))
    (hode : ∀ y ∈ U, ∀ k, HasDerivAt
      (fun z : ℂ => cotangentChart y.val.1 (Φ k (z, y)).val)
      (cotangentVectorOfCoords (Z k y.val)) 0)
    (y : NativeCotangentPoint M) (hy : y ∈ U) (k : Fin b) :
    fderiv ℂ (fun τ : Fin b → ℂ => cotangentChart y.val.1
      (finiteFlowCompose b Φ (y, τ)).val) 0 (Pi.single k 1) =
        cotangentVectorOfCoords (Z k y.val) := by
  classical
  have hpair : ContMDiff 𝓘(ℂ, Fin b → ℂ)
      ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, Fin b → ℂ)) ∞
      (fun τ : Fin b → ℂ => (y, τ)) := contMDiff_const.prodMk contMDiff_id
  have hslice := (hΨ.contMDiffAt ((hU.prod isOpen_ball).mem_nhds
    (show (y, 0) ∈ U ×ˢ ball (0 : Fin b → ℂ) R from ⟨hy, mem_ball_self hR⟩))).comp
      0 hpair.contMDiffAt
  have hc := (contMDiffAt_iff_target.mp hslice).2
  change ContMDiffAt 𝓘(ℂ, Fin b → ℂ) 𝓘(ℂ, CotangentCoord n) ∞
    (fun τ => cotangentChart (finiteFlowCompose b Φ (y, 0)).val.1
      (finiteFlowCompose b Φ (y, τ)).val) 0 at hc
  rw [finiteFlowCompose_zero b Φ hzero y] at hc
  have hdiff := hc.contDiffAt.differentiableAt (by simp)
  have hline := holomorphic_line_hasDerivAt hdiff (Pi.single k 1)
  have heq : (fun z : ℂ => cotangentChart y.val.1
      (finiteFlowCompose b Φ (y, 0 + z • Pi.single k 1)).val) =
      (fun z : ℂ => cotangentChart y.val.1 (Φ k (z, y)).val) := by
    funext z
    have hv : (z • Pi.single k 1 : Fin b → ℂ) = Pi.single k z := by
      funext j
      by_cases hj : j = k
      · subst j; simp
      · simp [Pi.single_apply, hj, Ne.symm hj]
    rw [zero_add, hv, finiteFlowCompose_single b Φ hzero y k z]
  rw [heq] at hline
  exact hline.deriv.symm.trans (hode y hy k).deriv

end Yau.Blueprint.V02FlowProof
