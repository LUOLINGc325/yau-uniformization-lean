import Yau.Proofs.V03RealDirichletBoundaryMixed
import Yau.Proofs.V03ActualLogMixedJet

/-! The original full logarithmic wall energy has its actual mixed
derivative bounded by native first-variation and mixed boundary traces. -/

open scoped Topology ContDiff

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem actualLogEnergy_bound_by_boundary_jets {n q : ℕ} {X : KahlerManifold n}
    {d : VariationData X q} (hd : VariationSetup d) (j : ℕ)
    {F : VariationDisc X} {fz : ℂ → ℂ → CotangentPoint X.manifold} {R : ℝ}
    (hfamily : HolomorphicDiscFamily F fz R)
    (hadm : ∀ z ∈ Metric.ball (0 : ℂ) R, AdmissibleVariationDisc d j {F with f := fz z}) :
    let f : ℂ × ℝ → ℂ := fun p => (logTrace d j (fz p.1) p.2 : ℂ)
    |mixedReal (fun z => (scalarDSq (logTrace d j (fz z))).toReal)| ≤
      (1 / 2 : ℝ) * ((boundaryDSq (fun θ (_ : Unit) => realParameterDerivative f 1 (0, θ))).toReal +
        (boundaryDSq (fun θ (_ : Unit) => realParameterDerivative f Complex.I (0, θ))).toReal) +
      2 * Real.sqrt (scalarDSq (logTrace d j F.f)).toReal *
        Real.sqrt (scalarDSq (fun θ => mixedReal (fun z => logTrace d j (fz z) θ))).toReal := by
  have hg := family_logTrace_joint_contDiffOn hd j hfamily hadm
  have hp : ∀ z ∈ Metric.ball (0 : ℂ) R,
      Function.Periodic (fun θ => logTrace d j (fz z) θ) (2 * Real.pi) :=
    fun z _ => logTrace_periodic d j {F with f := fz z}
  have hb := abs_mixedReal_scalarDSq_le_actual_mixed Metric.isOpen_ball hg hp
    (Metric.mem_ball_self hfamily.1)
  simpa only [hfamily.2.1] using hb

end Yau.Blueprint.V03Proof
