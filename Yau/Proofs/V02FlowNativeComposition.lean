import Yau.Proofs.V02FlowNativeFinite
import Yau.Proofs.V02FlowComposition

/-! The same initial chart controls every intermediate finite composition. -/

open scoped Manifold Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02FlowProof
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem finiteFlowCompose_native_decode
    (b : ℕ) (x : M.Carrier) (a : CotangentCoord n) {d T ρ A : ℝ}
    (φ : Fin b → ℂ × CotangentCoord n → CotangentCoord n)
    (Φ : Fin b → ℂ × NativeCotangentPoint M → NativeCotangentPoint M)
    (hball : ball a d ⊆ cotangentTarget x) (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hbranch : ∀ k t, t ∈ ball (0 : ℂ) T → ∀ y,
      y ∈ nativeCotangentChartBall x a d → Φ k (t, y) = nativeChartFlow x (φ k) (t, y))
    (hstep : ∀ k t u, ‖t‖ ≤ ρ → u ∈ ball a d → dist (φ k (t, u)) u ≤ ρ * A)
    {u : CotangentCoord n} {τ : Fin b → ℂ}
    (hτ : ∀ k, ‖τ k‖ ≤ ρ) (hτT : ∀ k, τ k ∈ ball (0 : ℂ) T)
    (hbudget : dist u a + (b : ℝ) * ρ * A < d) :
    finiteFlowCompose b Φ (NativeCotangentPoint.mk (cotangentChartInv x u), τ) =
      NativeCotangentPoint.mk (cotangentChartInv x (finiteFlowCompose b φ (u, τ))) := by
  induction b generalizing u with
  | zero => rfl
  | succ b ih =>
    have hu : u ∈ ball a d := mem_ball.mpr
      (lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hbudget)
    have hfirst := hstep 0 (τ 0) u (hτ 0) hu
    have hnext : dist (φ 0 (τ 0, u)) a + (b : ℝ) * ρ * A < d := by
      have htri := dist_triangle (φ 0 (τ 0, u)) u a
      push_cast at hbudget
      nlinarith
    have hn : NativeCotangentPoint.mk (cotangentChartInv x u) ∈
        nativeCotangentChartBall x a d := ⟨u, hu, rfl⟩
    have heq : Φ 0 (τ 0, NativeCotangentPoint.mk (cotangentChartInv x u)) =
        NativeCotangentPoint.mk (cotangentChartInv x (φ 0 (τ 0, u))) := by
      rw [hbranch 0 (τ 0) (hτT 0) _ hn]
      change NativeCotangentPoint.mk
        (cotangentChartInv x (φ 0 (τ 0, cotangentChart x (cotangentChartInv x u)))) = _
      rw [cotangentChart_right_inv x (hball hu)]
    simp only [finiteFlowCompose, heq]
    exact ih (fun k => φ k.succ) (fun k => Φ k.succ) (fun k => hbranch k.succ)
      (fun k => hstep k.succ) (fun k => hτ k.succ) (fun k => hτT k.succ) hnext

theorem native_decode_parameter_map_contMDiffOn
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (x : M.Carrier) {a : CotangentCoord n} {d : ℝ} {D : Set P}
    {ψ : CotangentCoord n × P → CotangentCoord n}
    (hball : ball a d ⊆ cotangentTarget x)
    (hψ : ContDiffOn ℂ ∞ ψ (ball a d ×ˢ D))
    (himage : ∀ p ∈ ball a d ×ˢ D, ψ p ∈ cotangentTarget x) :
    ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, P)) 𝓘(ℂ, CotangentCoord n) ∞
      (fun p : NativeCotangentPoint M × P =>
        NativeCotangentPoint.mk (cotangentChartInv x (ψ (cotangentChart x p.1.val, p.2))))
      (nativeCotangentChartBall x a d ×ˢ D) := by
  let S := nativeCotangentChartBall x a d ×ˢ D
  have hsource : ∀ p ∈ S, p.1.val ∈ cotangentSource x :=
    fun p hp => ((nativeCotangentChartBall_mem_iff hball).mp hp.1).1
  have hcoord : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, P))
      𝓘(ℂ, CotangentCoord n) ∞
      (fun p : NativeCotangentPoint M × P => cotangentChart x p.1.val) S :=
    (nativeCotangentChart_contMDiffOn x).comp contMDiffOn_fst hsource
  have hpair : ContMDiffOn ((𝓘(ℂ, CotangentCoord n)).prod 𝓘(ℂ, P))
      𝓘(ℂ, CotangentCoord n × P) ∞
      (fun p : NativeCotangentPoint M × P => (cotangentChart x p.1.val, p.2)) S := by
    apply (contMDiffOn_prod_module_iff _).mpr
    exact ⟨hcoord, contMDiffOn_snd⟩
  have hmap : ∀ p ∈ S, (cotangentChart x p.1.val, p.2) ∈ ball a d ×ˢ D :=
    fun p hp => ⟨((nativeCotangentChartBall_mem_iff hball).mp hp.1).2, hp.2⟩
  exact (nativeCotangentChartInv_contMDiffOn x).comp
    (hψ.contMDiffOn.comp hpair hmap) (fun p hp => himage _ (hmap p hp))

end Yau.Blueprint.V02FlowProof
