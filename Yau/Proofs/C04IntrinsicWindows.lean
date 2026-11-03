import Yau.Proofs.C04CentralSequence
import Yau.Proofs.C04RescaledTube

/-! The same selected clock windows, with one common tail for every intrinsic
curvature tube. The holomorphic-chart construction is a subsequent step. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint BlueprintContracts

theorem intrinsic_windows_of_originalC01_C02_C03
    (hC01 : C01_contract) (hC02 : C02_contract) (hC03 : C03_contract) :
    ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X),
    LocalizedFlow X o h U P ρ →
    ∃ a b, 0 < a ∧ a < 1 ∧ 0 < b ∧
      (∃ T, ∀ t u, T ≤ t → 0 ≤ u → ρ o u = a * ρ o t →
        b * clockSpeed o h u ≤ ricciMin o h t) ∧
      ∃ S : ℕ → ℝ, ∃ K : ℝ, Tendsto S atTop atTop ∧
        (∀ i t u, 0 ≤ t → 0 ≤ u → ρ o t = 2 * S i → ρ o u = a * S i →
          clockSpeed o h t ≤ K * clockSpeed o h u) ∧
        ∃ tw : ℕ → ℝ, (∀ i, 0 < tw i) ∧ Tendsto tw atTop atTop ∧
          (∀ i, 5 * S i / 4 ≤ ρ o (tw i) ∧ ρ o (tw i) ≤ 7 * S i / 4) ∧
          Tendsto (fun i => deriv (clockSpeed o h) (tw i) /
            (clockSpeed o h (tw i) * scalarCurvature (h (tw i)) o)) atTop (𝓝 0) ∧
          ∃ θ, 0 < θ ∧ ∃ lambda0, 0 < lambda0 ∧
            (∀ i, 0 < scalarCurvature (h (tw i)) o) ∧
            (∀ i (hR : 0 < scalarCurvature (h (tw i)) o),
              let g0 := scaleField (scalarCurvature (h (tw i)) o) hR (h (tw i))
              scalarCurvature g0 o = 1 ∧ lambda0 ≤ relMinEigenvalue (gMat g0 o) (ricci g0 o)) ∧
            ∀ r, 0 < r → ∃ b, 0 < b ∧ ∃ Kjet : ℕ → ℝ, (∀ m, 0 < Kjet m) ∧
              ∀ i (hRi : 0 < scalarCurvature (h (tw i)) o),
                ∀ p ∈ distBall (scaleField (scalarCurvature (h (tw i)) o) hRi (h (tw i))) o r,
                  ∀ z, |z| < θ →
                    let R := scalarCurvature (h (tw i)) o
                    let k := scaleField R hRi (h (tw i + z / R))
                    0 < tw i + z / R ∧ MetricSmooth k ∧ KahlerClosed k ∧
                      IsCompleteDistance (lengthDist k) ∧
                      ∀ m x, x ∈ distBall k p (2 * b) → curvatureJetNorm k m x ≤ Kjet m := by
  intro n X o h U P ρ hf
  have hH := hC01 n X o h U P ρ hf
  obtain ⟨a, b, ha, ha1, hb, hmin, S, K, hK, hSinf, hwindow, tw, htwpos, htwinf,
    hmiddle, hratio, l, hl, hRpos, hcenter⟩ := central_window_sequence X o h U P ρ hf hH
      (hC02 n X o h U P ρ hf) (hC03 n X)
  obtain ⟨θ, hθ, N, htube⟩ := C04RescaledTubeAux.rescaled_central_ball_curvature_jets
    X o h U P ρ hf hH a K ha ha1 hK S tw hSinf hwindow htwpos htwinf hmiddle
  let S' := fun i : ℕ => S (i + N)
  let tw' := fun i : ℕ => tw (i + N)
  have hshift : Tendsto (fun i : ℕ => i + N) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_add_right i N) tendsto_id
  refine ⟨a, b, ha, ha1, hb, hmin, S', K, hSinf.comp hshift, (fun i => hwindow (i + N)),
    tw', (fun i => htwpos (i + N)), htwinf.comp hshift, (fun i => hmiddle (i + N)),
    hratio.comp hshift, θ, hθ, l, hl, (fun i => hRpos (i + N)), (fun i => hcenter (i + N)), ?_⟩
  intro r hr
  obtain ⟨b', hb', Kjet, hKjet, hjets⟩ := htube r hr
  refine ⟨b', hb', Kjet, hKjet, ?_⟩
  intro i hRi p hp z hz
  exact hjets (i + N) (Nat.le_add_left N i) hRi p hp z hz

end Yau.Proofs.C04Aux
