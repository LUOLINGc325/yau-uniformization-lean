import Yau.Proofs.V03JointBaseTwoFormRegularity
import Yau.Proofs.V03JointBaseDensity
import Yau.Proofs.V03ClosedFormDiscCurrent

/-! The actual original base area of a jointly holomorphic family has
mixed derivative exactly the native boundary radial Kähler current. -/

open scoped Manifold Topology ContDiff
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem baseArea_joint_eq_discIntegral {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {f : ℂ × ℂ → CotangentPoint M} {U : Set ℂ}
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) :
    (discArea g.form (fun ζ => (f (z, ζ)).1)).toReal = ∫ ζ in Metric.ball (0 : ℂ) 1,
      jointBaseTwoForm g.form f (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ)
        ![((0, 1) : ℂ × ℂ), ((0, Complex.I) : ℂ × ℂ)] := by
  have hs : CotangentDisc (fun ζ => f (z, ζ)) :=
    (hf.comp (contDiff_const.prodMk contDiff_id) (fun ζ hζ => ⟨hz, hζ⟩)).cotangentDisc
  rw [discArea_eq_ofReal_integral g hs, ENNReal.toReal_ofReal
    (integral_nonneg (fun ζ => baseDensityWithin_nonneg g.form (fun η => f (z, η)) ζ))]
  apply setIntegral_congr_fun measurableSet_ball
  intro ζ hζ
  exact (jointBaseTwoForm_spatial_diagonal g.form hf hz (Metric.ball_subset_closedBall hζ)).symm

theorem baseArea_mixed_eq_boundary_current {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hK : IsKahler g)
    {f : ℂ × ℂ → CotangentPoint M} {U : Set ℂ} (hU : IsOpen U)
    (hf : CotangentHolomorphicOn f (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    (h0 : (0 : ℂ) ∈ U) :
    mixedReal (fun z => (discArea g.form (fun ζ => (f (z, ζ)).1)).toReal) =
      (1 / 4 : ℝ) * ∫ θ in (-Real.pi)..Real.pi,
        closedRealGradient (fun ζ => jointBaseTwoForm g.form f
          (U ×ˢ Metric.closedBall (0 : ℂ) 1) (0, ζ)
          ![((1, 0) : ℂ × ℂ), ((Complex.I, 0) : ℂ × ℂ)])
          (circlePoint θ) (circlePoint θ) := by
  have hS : UniqueDiffOn ℂ (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    hU.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have heq : (fun z => (discArea g.form (fun ζ => (f (z, ζ)).1)).toReal) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => ∫ ζ in Metric.ball (0 : ℂ) 1,
        jointBaseTwoForm g.form f (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, ζ)
          ![((0, 1) : ℂ × ℂ), ((0, Complex.I) : ℂ × ℂ)]) := by
    filter_upwards [hU.mem_nhds h0] with z hz
    exact baseArea_joint_eq_discIntegral g hf hz
  rw [mixedReal_congr heq]
  apply mixedReal_closedJForm_discIntegral_eq_current hU
    (jointBaseTwoForm_contDiffOn g hf hS) ?_ ?_ h0
  · intro p hp
    apply jointBaseTwoForm_closed g hK hf hS
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset ((hU.prod Metric.isOpen_ball).mem_nhds hp)
      (fun r hr => ⟨hr.1, Metric.ball_subset_closedBall hr.2⟩)
  · intro p hp u v
    exact jointBaseTwoForm_J g.form f _ p u v

end Yau.Blueprint.V03Proof
