import Yau.Proofs.V03JointGaussTwoFormClosed
import Yau.Proofs.V03JointGaussDensity
import Yau.Proofs.V03ClosedFormDiscCurrent

/-! The actual Gauss area of a joint original closed-disc family has
mixed derivative exactly its native boundary radial current. -/

open scoped Manifold Topology ContDiff
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem gaussArea_joint_eq_discIntegral {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : ℂ × ℂ → CotangentPoint M} {U : Set ℂ}
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) :
    gaussArea G (fun ζ => f (z, ζ)) = ∫ ζ in Metric.ball (0 : ℂ) 1,
      jointGaussTwoForm G f (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ)
        ![((0, 1) : ℂ × ℂ), ((0, Complex.I) : ℂ × ℂ)] := by
  rw [gaussArea_eq_integral_densityWithin]
  apply setIntegral_congr_fun measurableSet_ball
  intro ζ hζ
  exact (jointGaussTwoForm_spatial_diagonal hG hf hz (Metric.ball_subset_closedBall hζ)).symm

theorem gaussArea_mixed_eq_boundary_current {n q : ℕ} {M : ComplexManifold n}
    {G : CotangentPoint M → ComplexVector q} (hG : CotangentImmersion G)
    {f : ℂ × ℂ → CotangentPoint M} {U : Set ℂ} (hU : IsOpen U)
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    (h0 : (0 : ℂ) ∈ U) :
    mixedReal (fun z => gaussArea G (fun ζ => f (z, ζ))) =
      (1 / 4 : ℝ) * ∫ θ in (-Real.pi)..Real.pi,
        closedRealGradient (fun ζ => jointGaussTwoForm G f
          (U ×ˢ Metric.closedBall (0 : ℂ) 1) (0, ζ)
          ![((1, 0) : ℂ × ℂ), ((Complex.I, 0) : ℂ × ℂ)])
          (circlePoint θ) (circlePoint θ) := by
  have hS : UniqueDiffOn ℂ (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    hU.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have heq : (fun z => gaussArea G (fun ζ => f (z, ζ))) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => ∫ ζ in Metric.ball (0 : ℂ) 1,
        jointGaussTwoForm G f (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ)
          ![((0, 1) : ℂ × ℂ), ((0, Complex.I) : ℂ × ℂ)]) := by
    filter_upwards [hU.mem_nhds h0] with z hz
    exact gaussArea_joint_eq_discIntegral hG hf hz
  rw [mixedReal_congr heq]
  apply mixedReal_closedJForm_discIntegral_eq_current hU
    (jointGaussTwoForm_contDiffOn hG hf hS) ?_ ?_ h0
  · intro p hp
    apply jointGaussTwoForm_closed hG hf hS
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((hU.prod Metric.isOpen_ball).mem_nhds hp)
      (fun r hr => ⟨hr.1, Metric.ball_subset_closedBall hr.2⟩)
  · intro p hp u v
    exact jointGaussTwoForm_J hG f _ p u v

end Yau.Blueprint.V03Proof
