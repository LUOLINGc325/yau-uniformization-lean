import Yau.Proofs.C04NormalEllipticModelScalarJets
import Yau.Proofs.C04NormalEllipticModelConnectionJets

/-! The exact scalar normal-model coefficients have one radius-independent
ellipticity constant and simultaneous coefficient bounds at every order. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux
open Yau
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

theorem exists_normal_elliptic_model_bounds (n : ℕ)
    (B : ℕ → ℝ) (hB : ∀ m, 0 < B m) :
    ∃ ell : ℝ, 0 < ell ∧ ∃ C : ℕ → ℝ, (∀ s, 0 < C s) ∧
      ∀ R : ℝ, 0 < R →
        ∀ (A : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n)
          (conn : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n),
          ContDiff ℝ ∞ A → ContDiff ℝ ∞ conn →
          (∀ x ∈ Metric.ball (0 : ComplexVector n) R,
            ‖A x - ContinuousLinearMap.id ℝ (ComplexVector n)‖ ≤ (1 / 4 : ℝ)) →
          (∀ m x, x ∈ Metric.ball (0 : ComplexVector n) R →
            ‖iteratedFDeriv ℝ m A x‖ ≤ B m ∧ ‖iteratedFDeriv ℝ m conn x‖ ≤ B m) →
          (∀ i j, ContDiffOn ℝ ∞ (fun x => normalEllipticPrincipal (A x).inverse i j)
            (Metric.ball (0 : ComplexVector n) R)) ∧
          (∀ i, ContDiffOn ℝ ∞
            (fun x => normalEllipticDrift (A x).inverse (coframeModelConnection A conn x) i)
            (Metric.ball (0 : ComplexVector n) R)) ∧
          (∀ x ∈ Metric.ball (0 : ComplexVector n) R,
            (normalEllipticPrincipal (A x).inverse).IsSymm ∧ ∀ v : RIdx n → ℝ,
              ell * ∑ i, (v i) ^ 2 ≤
                ∑ i, ∑ j, normalEllipticPrincipal (A x).inverse i j * v i * v j) ∧
          (∀ s k, k ≤ s + 1 → ∀ x ∈ Metric.ball (0 : ComplexVector n) R, ∀ i j,
            ‖iteratedFDeriv ℝ k (fun y => normalEllipticPrincipal (A y).inverse i j) x‖ ≤ C s ∧
            ‖iteratedFDeriv ℝ k
              (fun y => normalEllipticDrift (A y).inverse (coframeModelConnection A conn y) i) x‖ ≤ C s) := by
  obtain ⟨P, hPpos, hPb⟩ := exists_normal_inverse_jet_bounds (E := ComplexVector n) B hB
  obtain ⟨Q, hQpos, hQb⟩ := exists_normal_connection_jet_bounds (E := ComplexVector n) B hB
  let CA : ℕ → ℝ := normalEllipticPrincipalJetBudget n P
  let CB : ℕ → ℝ := normalEllipticDriftJetBudget n P Q
  have hCA (m : ℕ) : 0 ≤ CA m :=
    normalEllipticPrincipalJetBudget_nonneg P (fun j => (hPpos j).le) m
  have hCB (m : ℕ) : 0 ≤ CB m :=
    normalEllipticDriftJetBudget_nonneg P Q (fun j => (hPpos j).le) (fun j => (hQpos j).le) m
  let C : ℕ → ℝ := fun s => 1 + ∑ k ∈ Finset.range (s + 2), (CA k + CB k)
  have hC (s : ℕ) : 0 < C s := by
    have hh : 0 ≤ ∑ k ∈ Finset.range (s + 2), (CA k + CB k) :=
      Finset.sum_nonneg fun k hk => add_nonneg (hCA k) (hCB k)
    dsimp [C]
    linarith
  have hsum {s k : ℕ} (hk : k ≤ s + 1) :
      CA k + CB k ≤ ∑ j ∈ Finset.range (s + 2), (CA j + CB j) :=
    Finset.single_le_sum (fun j hj => add_nonneg (hCA j) (hCB j))
      (Finset.mem_range.mpr (by omega))
  have hCAle {s k : ℕ} (hk : k ≤ s + 1) : CA k ≤ C s := by
    have hh := hsum hk
    have hb := hCB k
    dsimp [C]
    linarith
  have hCBle {s k : ℕ} (hk : k ≤ s + 1) : CB k ≤ C s := by
    have hh := hsum hk
    have ha := hCA k
    dsimp [C]
    linarith
  refine ⟨1 / 8, by norm_num, C, hC, ?_⟩
  intro R hR A conn hA hconn hnear hjet
  obtain ⟨hinv, hInvBound⟩ := hPb R hR A hA hnear (fun m x hx => (hjet m x hx).1)
  obtain ⟨hGamma, hGammaBound⟩ := hQb R hR A conn hA hconn hnear hjet
  refine ⟨(fun i j => normal_elliptic_principal_smooth _ hinv i j),
    (fun i => normal_elliptic_drift_smooth _ _ hinv hGamma i),
    (fun x hx => normal_elliptic_principal_ellipticity (A x) (hnear x hx)), ?_⟩
  intro s k hk x hx i j
  exact ⟨(normal_elliptic_principal_jet _ hinv Metric.isOpen_ball hx P
      (fun r => (hPpos r).le) (fun r => hInvBound r x hx) k i j).trans (hCAle hk),
    (normal_elliptic_drift_jet _ _ hinv hGamma Metric.isOpen_ball hx P Q
      (fun r => (hPpos r).le) (fun r => (hQpos r).le) (fun r => hInvBound r x hx)
      (fun r => hGammaBound r x hx) k i).trans (hCBle hk)⟩

end Yau.Proofs.C04Aux
