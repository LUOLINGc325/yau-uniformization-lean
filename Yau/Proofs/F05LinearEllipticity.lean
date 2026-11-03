import Yau.Proofs.F05LinearCoefficients
import Yau.Proofs.F05CoefficientEllipticity
import Yau.Proofs.F05PositiveScalar

/-! A genuinely positive smooth scalar and the actual metric family give
common ellipticity constants before every moving endpoint and chart. -/

open Set
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_positive_pull_bounds {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (c : M.Carrier → ℝ → ℝ) {S : ℝ} (hS : 0 < S)
    (hc : SmoothSpaceTime c (Icc 0 S)) (hPos : ∀ x t, t ∈ Icc 0 S → 0 < c x t)
    (i : Fin A.count) :
    ∃ l b : ℝ, 0 < l ∧ l ≤ b ∧ ∀ p ∈ cylinder (Metric.closedBall 0 2) 0 S,
      l ≤ pull A i c p ∧ pull A i c p ≤ b := by
  have hQ : IsCompact (cylinder (Metric.closedBall (0 : Space n) 2) 0 S) :=
    (isCompact_closedBall (0 : Space n) 2).prod isCompact_Icc
  have hNE : (cylinder (Metric.closedBall (0 : Space n) 2) 0 S).Nonempty := by
    refine ⟨(0,0),?_⟩
    simp [cylinder,hS.le]
  have hContinuous := (F05_pull_spacetime_smooth hA c hc i).continuousOn.mono
    (show cylinder (Metric.closedBall (0 : Space n) 2) 0 S ⊆ Metric.ball 0 3 ×ˢ Icc 0 S from
      fun p hp => ⟨Metric.closedBall_subset_ball (by norm_num : (2 : ℝ) < 3) hp.1,hp.2⟩)
  exact F05_compact_positive_bounds hQ hNE hContinuous (fun p hp => hPos _ _ hp.2)

theorem F05_linear_coefficients_elliptic_uniform {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hc : SmoothSpaceTime c (Icc 0 S)) (hPos : ∀ x t, t ∈ Icc 0 S → 0 < c x t) :
    ∃ lam upper : ℝ, ∀ (T : ℝ), T ≤ S → ∀ i : Fin A.count,
      Elliptic (cylinder (Metric.closedBall 0 2) 0 T)
        (fun p => pull A i c p • flatA (h p.2) A i p) lam upper := by
  classical
  let Q : Set (Point n) := cylinder (Metric.closedBall 0 2) 0 S
  have hEach (i : Fin A.count) : ∃ lam upper : ℝ,
      Elliptic Q (fun p => pull A i c p • flatA (h p.2) A i p) lam upper := by
    obtain ⟨lam,upper,hMetric⟩ := F05_flat_principal_elliptic_chart hA h hh i
    obtain ⟨l,b,hl,hlb,hScalar⟩ := F05_positive_pull_bounds hA c hS hc hPos i
    exact ⟨l*lam,b*upper,F05_elliptic_scalar_mul hMetric hl hlb hScalar⟩
  obtain ⟨lam,upper,hCommon⟩ := F05_uniform_elliptic_family
    (fun _ : Fin A.count => Q) (fun i p => pull A i c p • flatA (h p.2) A i p) hEach
  refine ⟨lam,upper,?_⟩
  intro T hTS i
  exact ⟨(hCommon i).1,(hCommon i).2.1,fun p hp =>
    (hCommon i).2.2 p ⟨hp.1,hp.2.1,hp.2.2.trans hTS⟩⟩

end Yau.Proofs.F05Aux
