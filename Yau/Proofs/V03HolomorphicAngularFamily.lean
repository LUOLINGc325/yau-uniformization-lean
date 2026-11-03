import Yau.Proofs.V03ComplexSlice
import Yau.Proofs.V03AngularDirichlet
import Yau.Proofs.V03EuclideanRadial
import Yau.Proofs.V03BoundaryDerivative
import Yau.Proofs.V03CirclePeriod

/-! The actual angular trace of a jointly holomorphic closed-disc family
is holomorphic as a uniform compact trace, hence also in the native
Dirichlet Hilbert space. -/

open scoped Topology ContDiff lp
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

def holomorphicBoundaryFamily (H : ℂ × ℂ → ℂ) (p : ℂ × ℝ) : ℂ := H (p.1, circlePoint p.2)

theorem holomorphicBoundaryFamily_contDiffOn {U : Set ℂ} {H : ℂ × ℂ → ℂ}
    (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℝ ∞ (holomorphicBoundaryFamily H) (U ×ˢ Set.univ) := by
  have hp : ContDiff ℝ ∞ (fun p : ℂ × ℝ => (p.1, circlePoint p.2)) :=
    contDiff_fst.prodMk (circlePoint_contDiff.comp contDiff_snd)
  exact (hH.restrict_scalars ℝ).comp hp.contDiffOn
    (fun p hp => ⟨hp.1, circlePoint_mem_closedBall p.2⟩)

theorem holomorphicBoundaryFamily_angular_eq {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) (θ : ℝ) :
    angularDerivative (holomorphicBoundaryFamily H) (z, θ) =
      fderivWithin ℂ H (U ×ˢ Metric.closedBall (0 : ℂ) 1) (z, circlePoint θ)
        (0, circlePoint θ * Complex.I) := by
  have hn := angularDerivative_hasDerivAt hU (holomorphicBoundaryFamily_contDiffOn hH) hz θ
  have hline : HasDerivAt (fun t : ℝ => (z, circlePoint t))
      ((0 : ℂ), circlePoint θ * Complex.I) θ :=
    (hasDerivAt_const (x := θ) (c := z)).prodMk (hasDerivAt_circlePoint θ)
  have hmap : ∀ᶠ t in 𝓝 θ, (z, circlePoint t) ∈ U ×ˢ Metric.closedBall (0 : ℂ) 1 :=
    Eventually.of_forall (fun t => ⟨hz, circlePoint_mem_closedBall t⟩)
  have hd := ((((hH.differentiableOn (by simp)) (z, circlePoint θ)
    ⟨hz, circlePoint_mem_closedBall θ⟩).hasFDerivWithinAt).restrictScalars ℝ).comp_hasDerivAt θ
      hline hmap
  exact hn.unique hd

theorem holomorphicBoundaryFamily_angular_parameter_differentiable {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) (θ : ℝ) :
    DifferentiableAt ℂ (fun p => angularDerivative (holomorphicBoundaryFamily H) (p, θ)) z := by
  have hS : UniqueDiffOn ℂ (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    hU.uniqueDiffOn.prod uniqueDiffOn_complex_closedDisc
  have hD : ContDiffOn ℂ ∞ (fun p => fderivWithin ℂ H
      (U ×ˢ Metric.closedBall (0 : ℂ) 1) p (0, circlePoint θ * Complex.I))
      (U ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    (hH.fderivWithin hS (m := ∞) (by simp)).clm_apply contDiffOn_const
  have hh := (hasFDerivAt_complex_parameter_slice hU hz (circlePoint_mem_closedBall θ)
    ((hD.differentiableOn (by simp)) _ ⟨hz, circlePoint_mem_closedBall θ⟩)).differentiableAt
  apply hh.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hz] with p hp
  exact holomorphicBoundaryFamily_angular_eq hU hH hp θ

theorem holomorphicAngularCompactTrace_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℂ ∞ (angularCompactTrace hU (holomorphicBoundaryFamily_contDiffOn hH)) U := by
  exact compactParamTrace_complex_contDiffOn hU (uniqueDiffOn_Icc (by positivity))
    ((angularDerivative_contDiffOn hU (holomorphicBoundaryFamily_contDiffOn hH)).mono
      (fun p hp => ⟨hp.1, Set.mem_univ _⟩))
    (fun p hp θ _ => holomorphicBoundaryFamily_angular_parameter_differentiable hU hH hp θ)

def holomorphicFamilyDirichletVector {U : Set ℂ} (hU : IsOpen U) {H : ℂ × ℂ → ℂ}
    (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) (z : ℂ) : ℓ²(ℤ, ℂ) :=
  angularDirichletVector hU (holomorphicBoundaryFamily_contDiffOn hH) z

theorem holomorphicFamilyDirichletVector_contDiffOn {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1)) :
    ContDiffOn ℂ ∞ (holomorphicFamilyDirichletVector hU hH) U := by
  exact intervalDirichletL.contDiff.comp_contDiffOn (holomorphicAngularCompactTrace_contDiffOn hU hH)

theorem holomorphicFamilyDirichletVector_norm_sq {U : Set ℂ} (hU : IsOpen U)
    {H : ℂ × ℂ → ℂ} (hH : ContDiffOn ℂ ∞ H (U ×ˢ Metric.closedBall (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ U) :
    ‖holomorphicFamilyDirichletVector hU hH z‖ ^ 2 =
      (boundaryDSq (fun θ (_ : Unit) => H (z, circlePoint θ))).toReal :=
  angularDirichletVector_norm_sq hU (holomorphicBoundaryFamily_contDiffOn hH) hz
    (circleTrace_periodic (fun ζ => H (z, ζ)))

end Yau.Blueprint.V03Proof
