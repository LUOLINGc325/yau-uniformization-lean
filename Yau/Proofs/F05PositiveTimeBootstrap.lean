import Yau.Proofs.F05BootstrapPositiveSmooth
import Yau.Proofs.F05PositiveSmoothTransfer
import Yau.Proofs.F05PositiveChartEquation
import Yau.Proofs.F05CoefficientEllipticity
import Yau.Proofs.F05LinearCoefficients

/-! The supplied nonlinear Schauder solution is actually jointly smooth on
all positive-time closed physical charts, including the full receiving rim. -/

open Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_positive_time_boundary_bootstrap (hn : 0 < n)
    {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A)
    (h : ℝ → HermitianField M) (R p w : M.Carrier → ℝ → ℝ)
    {T α K : ℝ} (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    (hh : MetricFamilySmooth h (Icc 0 T))
    (hR : SmoothSpaceTime R (Icc 0 T)) (hp : SmoothSpaceTime p (Icc 0 T))
    (hWCont : ContinuousOn (fun z : M.Carrier × ℝ => w z.1 z.2) (closure O ×ˢ Icc 0 T))
    (hW : ∀ i, SchauderBound α (F05Q A i T) (pull A i w) K)
    (hInitial : ∀ x ∈ closure O, w x 0 = p x 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = p x t)
    (hEquation : ∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
      derivWithin (w x) (Icc 0 T) t =
        Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
          (1-Real.exp (-w x t))*R x t) :
    ∀ τ : ℝ, 0 < τ → τ < T → ∀ i,
      ContDiffOn ℝ ∞ (pull A i w) (F05D A i ×ˢ Icc τ T) := by
  intro τ hτ hτT
  apply F05_positive_inner_smooth_to_full hA w
  intro i
  have hBackground : Metric.ball (0 : Space n) 3 ×ˢ Ioc 0 T ⊆
      Metric.ball 0 3 ×ˢ Icc 0 T := prod_mono subset_rfl Ioc_subset_Icc_self
  have hMetric := F05_flat_coefficients_smooth hA h hh i
  have hRChart := F05_pull_spacetime_smooth hA R hR i
  have hpChart := F05_pull_spacetime_smooth hA p hp i
  have hLocal := F05_native_schauder_local_relative (A.normal i) hα hα1 (hW i)
  have hFace : F05ZeroFace (A.normal i) T (fun z => pull A i w z-pull A i p z) := by
    unfold F05ZeroFace
    cases hν : A.normal i with
    | none => trivial
    | some j =>
      intro x hx hzero t ht
      have hx3 := Metric.ball_subset_ball (by norm_num : (2 : ℝ) ≤ 3) hx
      have hPhysical := ((hA.1 i).2.2.2.2.2.2.2 x hx3).2.2
      have hFront : lift A i x ∈ frontier O := hPhysical.mpr (by simpa only [hν] using hzero)
      exact sub_eq_zero.mpr (hBoundary (lift A i x) hFront t ⟨ht.1.le,ht.2⟩)
  obtain ⟨lam,upper,hEll⟩ := F05_flat_principal_elliptic_chart hA h hh i
  have hCap : F05PosPatch (A.normal i) T ⊆ F05Q A i T := by
    intro z hz
    refine ⟨F05_posSpace_mem_region hz.1 ?_,hz.2.1.le,hz.2.2⟩
    simpa only [dist_zero_right] using (Metric.mem_ball.mp hz.1.2).le
  have hEllPos : Elliptic (F05PosPatch (A.normal i) T)
      (fun z => flatA (h z.2) A i z) lam upper := by
    refine ⟨hEll.1,hEll.2.1,?_⟩
    intro z hz
    exact hEll.2.2 z ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using (hCap hz).1.1,(hCap hz).2⟩
  exact F05_flat_nonlinear_positive_cap_smooth hT hα hα1 (hW i).2.1
    (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (3/2 : ℝ) < 2) hτ hτT.le
    (fun z => flatA (h z.2) A i z) (fun z => flatB (h z.2) A i z)
    (pull A i R) (pull A i p) (pull A i w)
    (hMetric.1.mono hBackground) (fun j => (hMetric.2 j).mono hBackground)
    (hRChart.mono hBackground) (hpChart.mono hBackground) hLocal hFace hEllPos
    (fun z hz => ((hW i).2.2.1 z (hCap hz)).1)
    (F05_original_nonlinear_chart_equation hA h R w i (hW i).1 hEquation)

end Yau.Proofs.F05Aux
