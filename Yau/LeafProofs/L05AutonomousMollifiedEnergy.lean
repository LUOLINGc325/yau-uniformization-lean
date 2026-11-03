import Yau.LeafProofs.L05AutonomousMollifiedTraceBounds
import Yau.LeafProofs.L05AutonomousLocalEnergy

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- Actual original-input trace bounds feed the proved elementary localized energy estimate. -/
theorem auto_uniform_mollified_energy :
    ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
    ∃ B E : ℝ, 0 < B ∧ 0 < E ∧
      ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L → ConcaveOn ℝ univ F → F 0=0 →
      ∃ A∈slopeSet n ell L,
        ∀ u : Point n → ℝ, ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p|≤ 1) →
        viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
        ∃ w : Point n →ᵇ ℝ, EqOn w u (unitClosed n) ∧ UniformContinuous (w : Point n → ℝ) ∧
          HasCompactSupport (w : Point n → ℝ) ∧ ‖w‖ ≤ 1 ∧
          ∀ (eps : ℝ) (heps : 0 < eps), eps < 1/64 →
            (∀ p∈autoClosed (0 : Space n) (3/4) 0,
              |Matrix.trace ((A : Mat n)*secondFDerivMatrix
                (fun x => autoSpatialMollify eps heps w (x,p.2)) p.1)| ≤ B) ∧
            (∀ t∈Icc (-(93/128 : ℝ)^2) 0,
              IntegrableOn (fun x => ‖secondFDerivMatrix (fun y => autoSpatialMollify eps heps w (y,t)) x‖^2)
                (Metric.ball (0 : Space n) (47/64)) ∧
              (∫ x in Metric.ball (0 : Space n) (47/64),
                ‖secondFDerivMatrix (fun y => autoSpatialMollify eps heps w (y,t)) x‖^2) ≤ E) := by
  intro n hn ell L hell hL
  obtain ⟨B,hB,hForF⟩ := auto_uniform_mollified_trace n hn ell L hell hL
  obtain ⟨K,hK,hEnergy⟩ := auto_local_hessian_energy n hell hL
    (by norm_num : (0 : ℝ) < 47/64) (by norm_num : (47/64 : ℝ) < 3/4)
  refine ⟨B,K*(1+B^2),hB,mul_pos hK (by positivity),?_⟩
  intro F hF hE hConc h0
  obtain ⟨A,hA,hForU⟩ := hForF F hF hE hConc h0
  refine ⟨A,hA,?_⟩
  intro u hu hb hsol
  obtain ⟨w,hwu,hw,hcw,hw1,hTrace⟩ := hForU u hu hb hsol
  refine ⟨w,hwu,hw,hcw,hw1,?_⟩
  intro eps heps hepsSmall
  refine ⟨hTrace eps heps hepsSmall,?_⟩
  intro t ht
  have hSmooth := autoSpatialMollify_spatial_contDiff eps heps w hw t
  have hBound (x : Space n) (_hx : x∈Metric.ball (0 : Space n) (3/4)) :
      |autoSpatialMollify eps heps w (x,t)| ≤ 1 := (autoSpatialMollify_abs_le eps heps w hw _).trans hw1
  have hTraceSlice (x : Space n) (hx : x∈Metric.ball (0 : Space n) (3/4)) :
      |Matrix.trace ((A : Mat n)*secondFDerivMatrix (fun y => autoSpatialMollify eps heps w (y,t)) x)| ≤ B :=
    hTrace eps heps hepsSmall (x,t) ⟨Metric.ball_subset_closedBall hx,by
      change (0 : ℝ)-(3/4)^2 ≤ t ∧ t ≤ 0
      exact ⟨by linarith only [ht.1],ht.2⟩⟩
  simpa only [one_pow] using hEnergy A hA 1 B (by norm_num) hB.le _ hSmooth hBound hTraceSlice

end Yau.LeafProofs.L05AutonomousAux
