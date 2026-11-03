import Yau.Proofs.C05DefectClock
import Yau.Proofs.C04RescaledTube

/-! Keep the original good sequence and its normalized Ricci pinching, and
apply the already proved intrinsic curvature tube theorem to that same sequence. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Filter
variable {n : ℕ} {X : KahlerManifold n}

theorem original_good_sequence_with_intrinsic_tubes (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (hW : RicciWindows X o h ρ) :
    ∃ tw : ℕ → ℝ, (∀ i, 0 < tw i) ∧ Tendsto tw atTop atTop ∧
      ∃ hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o,
        ∃ lam : ℝ, 0 < lam ∧
          (∀ i, let k := scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))
            scalarCurvature k o = 1 ∧ lam ≤ relMinEigenvalue (gMat k o) (ricci k o)) ∧
          Tendsto (fun i => scalarHarnackSum h o (tw i) /
            scalarCurvature (h (tw i)) o ^ 2) atTop (𝓝 0) ∧
          ∃ θ : ℝ, 0 < θ ∧ ∃ N : ℕ, ∀ r : ℝ, 0 < r →
            ∃ b : ℝ, 0 < b ∧ ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
              ∀ i : ℕ, N ≤ i →
                ∀ p ∈ distBall (scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))) o r,
                  ∀ z : ℝ, |z| < θ →
                    let R := scalarCurvature (h (tw i)) o
                    let k := scaleField R (hRi i) (h (tw i + z / R))
                    0 < tw i + z / R ∧ MetricSmooth k ∧ KahlerClosed k ∧
                      IsCompleteDistance (lengthDist k) ∧
                        ∀ m : ℕ, ∀ x ∈ distBall k p (2 * b), curvatureJetNorm k m x ≤ C m := by
  rcases hW.2.2.2.2.2.2.2 with
    ⟨a, b, ha, ha1, hb, hcross, S, K0, hS, hspeed, tw, htw, htwinf,
      hmiddle, hgood, θ0, hθ0, lam, hlam, hRi, hnorm, hcharts⟩
  let K := max 1 K0
  have hK : 1 ≤ K := le_max_left _ _
  have hwindow : ∀ i t t', 0 ≤ t → 0 ≤ t' → ρ o t = 2 * S i →
      ρ o t' = a * S i → clockSpeed o h t ≤ K * clockSpeed o h t' := by
    intro i t t' ht ht' hs hs'
    apply (hspeed i t t' ht ht' hs hs').trans
    apply mul_le_mul_of_nonneg_right (le_max_right _ _)
    exact mul_nonneg ht' (scalar_pos X o h hH ht' o).le
  obtain ⟨θ, hθ, N, htube⟩ := rescaled_central_ball_curvature_jets
    X o h U P ρ hf hH a K ha ha1 hK S tw hS hwindow htw htwinf hmiddle
  refine ⟨tw, htw, htwinf, hRi, lam, hlam, ?_, ?_, θ, hθ, N, ?_⟩
  · exact fun i => hnorm i (hRi i)
  · exact normalized_center_defect_tendsto o h U P ρ hf tw htw hRi hgood
  · intro r hr
    obtain ⟨b, hb, C, hC, hjet⟩ := htube r hr
    exact ⟨b, hb, C, hC, fun i hi p hp z hz => hjet i hi (hRi i) p hp z hz⟩

end Yau.Proofs.C05Aux
