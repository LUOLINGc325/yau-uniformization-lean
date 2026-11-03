import Yau.Proofs.V03EuclideanAreaVariation
import Yau.Proofs.V03VelocityBounds

/-! The actual prescribed first ambient velocity inherits holomorphic
closed-disc regularity from the genuine joint realization, without an extra premise. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem realized_ambientVelocity_contDiffOn {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j a : ℕ)
    (F : VariationDisc X) (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (R : ℝ)
    (hR : RealizesFirstField d j a F E l h α fz R) :
    ContDiffOn ℂ ∞ (ambientVelocity d F E l h α) (Metric.closedBall (0 : ℂ) 1) := by
  let U : Set ℂ := Metric.ball 0 R
  let H : ℂ × ℂ → ComplexVector q := fun p => d.G (fz p.1 p.2)
  have h0 : (0 : ℂ) ∈ U := Metric.mem_ball_self hR.1.1
  have hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    cotangentHolomorphicOn_ambient_contDiffOn hR.1.2.2 hd.2.2.2.2.1.1
  have hS : UniqueDiffOn ℂ (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    Metric.isOpen_ball.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have hD := (hH.fderivWithin hS (m := ∞) (by simp)).clm_apply
    (contDiffOn_const (c := ((1, 0) : ℂ × ℂ)))
  have hV : ContDiffOn ℂ ∞
      (fun ζ => fderivWithin ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) (0, ζ) (1, 0))
      (Metric.closedBall (0 : ℂ) 1) :=
    hD.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun ζ hζ => ⟨h0, hζ⟩)
  apply hV.congr
  intro ζ hζ
  have hh := fderiv_complex_parameter_slice (U := U) Metric.isOpen_ball h0 hζ
    ((hH.differentiableOn (by simp)) _ ⟨h0, hζ⟩) (1 : ℂ)
  rw [← hh]
  exact (realizes_ambient_first_derivative d hd j a F E l h α fz R hR ζ hζ).symm

end Yau.Blueprint.V03Proof
