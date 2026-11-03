import Yau.Proofs.C04BoundedGeometryChartsNormalCoordinateFunction
import Yau.Proofs.C04BoundedGeometryChartsCoordinateHarmonic
import Yau.Proofs.C04BoundedGeometryChartsScaledJetBounds
import Yau.Proofs.C04BoundedGeometryChartsHarmonicVectorBounds
import Yau.Proofs.C04NormalEllipticModel

/-! The SAME actual NN coordinate function has uniform bounds at every order. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix.Norms.Elementwise
namespace Yau.Proofs.C04ChartsAux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

theorem normalEllipticPrincipal_eq_frame {n : ℕ} (B : ComplexVector n →L[ℝ] ComplexVector n) :
    C04Aux.normalEllipticPrincipal B = framePrincipalCoefficients B := rfl

theorem normalEllipticDrift_eq_frame {n : ℕ} (B : ComplexVector n →L[ℝ] ComplexVector n)
    (G : ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n) :
    C04Aux.normalEllipticDrift B G = frameDriftCoefficients B G := rfl

theorem exists_uniform_normal_coordinate_jet_bounds (n : ℕ) (hn : 0 < n)
    (r : ℝ) (K : ℕ → ℝ) (hr : 0 < r) (hK : ∀ m, 0 < K m) :
    ∃ R : ℝ, 0 < R ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ d ≤ R / 4 ∧
      ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧
      ∀ (M : ComplexManifold n) (g : SmoothMetric M), KahlerClosed g.form →
      ∀ (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p),
        (∀ i j, (g.form p).toFun (U (stdVec i)) (U (stdVec j)) =
          (1 : Matrix (Fin n) (Fin n) ℂ) i j) →
        (∀ m x, x ∈ distBall g.form p (2 * r) → curvatureJetNorm g.form m x ≤ K m) →
        (∀ x ∈ Metric.closedBall (0 : ComplexVector n) R,
          unitaryExponential g p U x ∈ distBall g.form p (2 * r) ∧
          ‖radialCoframe g p U x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ) ∧
          (realMapDeriv (unitaryExponential g p U) x).IsInvertible) ∧
        (∀ m x, x ∈ Metric.closedBall (0 : ComplexVector n) R →
          ‖iteratedFDeriv ℝ m (radialCoframe g p U) x‖ ≤ B m ∧
          ‖iteratedFDeriv ℝ m (radialConnection g p U) x‖ ≤ B m ∧
          ‖iteratedFDeriv ℝ m (radialCurvatureOperator g p U) x‖ ≤ B m) ∧
        ∃ F : ComplexVector n → ComplexVector n, ContDiff ℝ ∞ F ∧ F 0 = 0 ∧
          (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ),
            ‖fderiv ℝ F x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ)) ∧
          (∀ x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ), ∀ v,
            fderiv ℝ F x (realPullbackJ (unitaryExponential g p U) (d • x) v) =
              Complex.I • fderiv ℝ F x v) ∧
          ∀ m x, x ∈ Metric.ball (0 : ComplexVector n) (1 / 4 : ℝ) →
            ‖iteratedFDeriv ℝ m F x‖ ≤ D m := by
  obtain ⟨R, hR, B, hB, d, hd, hd1, hdR, hcoords⟩ :=
    exists_uniform_normal_coordinate_function n hn r K hr hK
  obtain ⟨ell, hell, C, hC, hcoeff⟩ := C04Aux.exists_normal_elliptic_model_bounds n B hB
  obtain ⟨D, hD, hFbound⟩ := exists_harmonic_vector_derivative_bounds n ell hell C hC
  refine ⟨R, hR, B, hB, d, hd, hd1, hdR, D, hD, ?_⟩
  intro M g hk p U hU hcurv
  obtain ⟨hseed, hjet, F, hF, hF0, hclose, hcomplex, hnorm⟩ := hcoords M g hk p U hU hcurv
  let A := scaledRadialCoframe g p U d
  let conn := scaledRadialConnection g p U d
  have hscaled : ∀ m x, x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ) →
      ‖iteratedFDeriv ℝ m A x‖ ≤ B m ∧ ‖iteratedFDeriv ℝ m conn x‖ ≤ B m :=
    scaled_normal_jets_le g p U R hR B d hd hd1 hdR (fun m x hx => ⟨(hjet m x hx).1, (hjet m x hx).2.1⟩)
  have hnear (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ)) :
      ‖A x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ) :=
    (hseed _ (dilate_half_ball_mem_closed hR hd hdR hx)).2.1
  have hi (x : ComplexVector n) (hx : x ∈ Metric.ball (0 : ComplexVector n) (1 / 2 : ℝ)) :
      (A x).IsInvertible := Yau.LeafProofs.L21Aux.isInvertible_of_norm_sub_id_lt_one _
        ((hnear x hx).trans_lt (by norm_num))
  have HH := hcoeff (1 / 2) (by norm_num) A conn (scaledRadialCoframe_smooth g p U d)
    (scaledRadialConnection_smooth g p U d) hnear hscaled
  simp only [normalEllipticPrincipal_eq_frame, normalEllipticDrift_eq_frame] at HH
  obtain ⟨ha, hb, hEll, hBounds⟩ := HH
  have h38 : Metric.ball (0 : ComplexVector n) (3 / 8 : ℝ) ⊆ Metric.ball 0 (1 / 2 : ℝ) :=
    Metric.ball_subset_ball (by norm_num)
  have hPDE (j : Fin n) : Set.EqOn
      (Yau.LeafCandidates.ellipticOp (fun y => framePrincipalCoefficients (A y).inverse)
        (fun y => frameDriftCoefficients (A y).inverse (C04Aux.coframeModelConnection A conn y))
        (fun y => F y j)) 0 (Metric.ball (0 : ComplexVector n) (3 / 8 : ℝ)) := by
    intro x hx
    exact normal_coordinate_component_elliptic g hk p U d F hF hi hcomplex j x (h38 hx)
  have hAll := hFbound _ _ (fun i j => (ha i j).mono h38) (fun i => (hb i).mono h38)
    (fun x hx => hEll x (h38 hx))
    (fun s k hk x hx i j => hBounds s k hk x (h38 hx) i j) F hF hnorm hPDE
  exact ⟨hseed, hjet, F, hF, hF0, hclose, hcomplex, hAll⟩

end Yau.Proofs.C04ChartsAux
