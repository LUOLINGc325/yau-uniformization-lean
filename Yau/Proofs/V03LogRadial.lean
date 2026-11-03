import Yau.Proofs.V03BoundaryUniform
import Yau.Proofs.V03RadialUniform
import Yau.Proofs.V03C1Dirichlet
import Yau.Proofs.V03DirichletEventual

/-! Radial convergence of the original logarithmic wall Fourier energy.
The full real logarithm is retained; its circle derivative supplies the
domination required for the infinite Fourier seminorm. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem radial_trace_contDiff {f : ℂ → ℝ} {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ θ, ContDiffWithinAt ℝ ∞ f (Metric.closedBall 0 1) ((r : ℂ) * circlePoint θ)) :
    ContDiff ℝ ∞ (fun θ => f ((r : ℂ) * circlePoint θ)) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  have hc : ContDiff ℝ ∞ (fun t => (r : ℂ) * circlePoint t) :=
    contDiff_const.mul circlePoint_contDiff
  have hh := (hf θ).comp θ hc.contDiffAt.contDiffWithinAt
    (fun t (_ : t ∈ (Set.univ : Set ℝ)) =>
      radial_maps_closedBall hr.1 hr.2 (circlePoint_mem_closedBall t))
  exact contDiffWithinAt_univ.mp hh

theorem complex_C1_radial_trace {f : ℂ → ℝ} {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ θ, ContDiffWithinAt ℝ ∞ f (Metric.closedBall 0 1) ((r : ℂ) * circlePoint θ)) :
    (∀ θ, HasDerivAt (fun t => (f ((r : ℂ) * circlePoint t) : ℂ))
      (angularWithinDerivative f r θ : ℂ) θ) ∧
    Continuous (fun θ => (angularWithinDerivative f r θ : ℂ)) ∧
    (f ((r : ℂ) * circlePoint (2 * Real.pi)) : ℂ) = (f ((r : ℂ) * circlePoint 0) : ℂ) := by
  have hU : ContDiff ℝ ∞ (fun θ => (f ((r : ℂ) * circlePoint θ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (radial_trace_contDiff hr hf)
  have hderiv (θ : ℝ) : HasDerivAt (fun t => (f ((r : ℂ) * circlePoint t) : ℂ))
      (angularWithinDerivative f r θ : ℂ) θ :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_radial_trace hr ((hf θ).differentiableWithinAt (by simp)))
  refine ⟨hderiv, ?_, ?_⟩
  · have heq : (fun θ => (angularWithinDerivative f r θ : ℂ)) =
        deriv (fun θ => (f ((r : ℂ) * circlePoint θ) : ℂ)) :=
      funext fun θ => (hderiv θ).deriv.symm
    rw [heq]
    exact hU.continuous_deriv (by simp)
  · simp only [circlePoint_two_pi, circlePoint_zero]

variable {n q : ℕ} {X : KahlerManifold n}

theorem admissible_logWall_radial_contDiff_eventually {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1, r ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ θ, ContDiffWithinAt ℝ ∞ (fun ζ => Real.log (wallProduct d j (F.f ζ)))
        (Metric.closedBall 0 1) ((r : ℂ) * circlePoint θ) := by
  obtain ⟨hA, hB⟩ := setup_index_bounds hd j
  filter_upwards [self_mem_nhdsWithin, radial_boundaryRegion_eventually hd hF] with r hr hb
  refine ⟨hr, fun θ => ?_⟩
  have hpt := radial_maps_closedBall hr.1 hr.2 (circlePoint_mem_closedBall θ)
  have hp := wallProduct_pos_le_one (setup_wallProfiles hd) hA hB (hb θ)
  exact ((cotangentDisc_wallProduct_contDiffOn hd j hF.1) _ hpt).log hp.1.ne'

theorem logSeminorm_radial_toReal_tendsto {d : VariationData X q}
    (hd : VariationSetup d) {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    Tendsto (fun r : ℝ => (scalarDSq (logTrace d j (radialVariationDisc F r).f)).toReal)
      (𝓝[Set.Icc 0 1] 1) (𝓝 (scalarDSq (logTrace d j F.f)).toReal) := by
  let q₀ : ℂ → ℝ := fun ζ => Real.log (wallProduct d j (F.f ζ))
  let U : ℝ → ℝ → ℂ := fun r θ => (q₀ ((r : ℂ) * circlePoint θ) : ℂ)
  let V : ℝ → ℝ → ℂ := fun r θ => (angularWithinDerivative q₀ r θ : ℂ)
  have hgood : ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1,
      (∀ θ, HasDerivAt (U r) (V r θ) θ) ∧ Continuous (V r) ∧ U r (2 * Real.pi) = U r 0 :=
    (admissible_logWall_radial_contDiff_eventually hd hF).mono fun r hr =>
      complex_C1_radial_trace hr.1 hr.2
  have hbase := complex_C1_radial_trace (f := q₀) (r := 1) (by simp)
    (fun θ => by simpa only [Complex.ofReal_one, one_mul] using
      admissible_logWall_contDiffWithinAt hd hF θ)
  have hreal := admissible_logWall_angular_uniform hd hF
  have hunif : TendstoUniformlyOn V (V 1) (𝓝[Set.Icc 0 1] 1) (Set.Icc 0 (2 * Real.pi)) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hreal) ε hε] with r hr
    intro θ hθ
    simpa only [V, q₀, Complex.isometry_ofReal.dist_eq] using hr θ hθ
  have hsub := boundaryDSq_sub_toReal_tendsto_of_uniform_derivative U V (U 1) (V 1)
    hgood hbase.1 hbase.2.1 hbase.2.2 hunif
  have hUC : Continuous (U 1) := continuous_iff_continuousAt.mpr fun θ =>
    (hbase.1 θ).continuousAt
  have hUF := boundaryDSq_ne_top_of_periodic_C1 hbase.1 hbase.2.1 hbase.2.2
  have hregular : ∀ᶠ r : ℝ in 𝓝[Set.Icc 0 1] 1,
      Continuous (U r) ∧ boundaryDSq (fun θ (_ : Unit) => U r θ) ≠ ⊤ :=
    hgood.mono fun r hr => ⟨continuous_iff_continuousAt.mpr (fun θ => (hr.1 θ).continuousAt),
      boundaryDSq_ne_top_of_periodic_C1 hr.1 hr.2.1 hr.2.2⟩
  have ht := boundaryDSq_toReal_tendsto_of_eventual_sub U (U 1) hregular hUC hUF hsub
  simpa only [U, q₀, logTrace, radialVariationDisc, Complex.ofReal_one, one_mul, scalarDSq] using ht

end Yau.Blueprint.V03Proof
