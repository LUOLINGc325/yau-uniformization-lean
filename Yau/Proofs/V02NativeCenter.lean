import Yau.Proofs.V02SprayCenterTube
import Yau.Proofs.V02NativeFamily

/-! Transfer the compact center tube to the literal original disc family. -/

open scoped Manifold Topology ContDiff
open Metric Set

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint V03Proof

variable {n b q : ℕ} {X : KahlerManifold n}

theorem nativeSprayFamily_center
    {d : VariationData X q}
    {Ψ : NativeCotangentPoint X.manifold × (Fin b → ℂ) →
      NativeCotangentPoint X.manifold}
    {Kc : Set (CotangentCoord n × ℝ)} {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hTube : ∀ p ∈ Kc, ∀ τ ∈ closedBall (0 : Fin b → ℂ) ρ,
      InCotangentTimeChart d.chart
        (Ψ (NativeCotangentPoint.mk (cotangentChartInv d.chart p.1), τ)).val p.2
        (interior (centerCylinder d)))
    {F : VariationDisc X} (hcenter : InCotangentTimeChart d.chart (F.f 0) F.s Kc)
    {h : ℂ → ℂ} (hh : ∀ ζ ∈ closedBall (0 : ℂ) 1, ‖h ζ‖ ≤ 1)
    {c : ℂ → Fin b → ℂ} (hc : ∀ ζ ∈ closedBall (0 : ℂ) 1, ∀ k, ‖c ζ k‖ ≤ C)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) (ρ / (2 * (C + 1)))) :
    InCotangentTimeChart d.chart (nativeSprayFamily Ψ F.f h c z 0) F.s
      (interior (centerCylinder d)) := by
  have hτ := nativeSprayFamily_parameter_bound (R := ρ) (C := C) hρ hC
    (h := h) hh (c := c) hc (p := (z, 0)) ⟨hz, by simp⟩
  have ht := hTube (cotangentChart d.chart (F.f 0), F.s) hcenter.2
    (fun k => z * h 0 * c 0 k) (ball_subset_closedBall hτ)
  rw [cotangentChart_left_inv d.chart hcenter.1] at ht
  exact ht

end Yau.Blueprint.V02Proof
