import Yau.Proofs.C05OriginalWindows
import Yau.Proofs.C05CurvatureScalarRicciBudget

/-! The original C04 sequence supplies one actual uniform order-six scalar
and Ricci budget on its original central intrinsic tubes. -/
noncomputable section
open scoped Topology Manifold ContDiff
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Filter
variable {n : ℕ} {X : KahlerManifold n}

theorem original_good_sequence_with_finite_jet_tubes (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (hW : RicciWindows X o h ρ) :
    ∃ tw : ℕ → ℝ, (∀ i, 0 < tw i) ∧ Tendsto tw atTop atTop ∧
      ∃ hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o,
        ∃ lam : ℝ, 0 < lam ∧
          (∀ i, let k := scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))
            scalarCurvature k o = 1 ∧ lam ≤ relMinEigenvalue (gMat k o) (ricci k o)) ∧
          Tendsto (fun i => scalarHarnackSum h o (tw i) /
            scalarCurvature (h (tw i)) o ^ 2) atTop (𝓝 0) ∧
          ∃ θ : ℝ, 0 < θ ∧ ∃ N : ℕ, ∃ b : ℝ, 0 < b ∧ ∃ B : ℝ, 0 < B ∧
            ∀ i : ℕ, N ≤ i →
              ∀ p ∈ distBall (scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))) o 1,
                ∀ z : ℝ, |z| < θ →
                  let R := scalarCurvature (h (tw i)) o
                  let k := scaleField R (hRi i) (h (tw i+z/R))
                  0 < tw i+z/R ∧ MetricSmooth k ∧ KahlerClosed k ∧
                    IsCompleteDistance (lengthDist k) ∧ ∀ x ∈ distBall k p (2*b),
                      (∀ m ≤ 6, scalarJetNorm k (scalarCurvature k) m x ≤ B) ∧
                      (∀ m ≤ 6, realRicciJetNorm k m x ≤ B) := by
  obtain ⟨tw,htw,htwinf,hRi,lam,hlam,hnorm,hdefect,θ,hθ,N,htube⟩ :=
    original_good_sequence_with_intrinsic_tubes o h U P ρ hf hH hW
  obtain ⟨b,hb,C,hC,hjet⟩ := htube 1 zero_lt_one
  obtain ⟨B,hB,hbudget⟩ := exists_uniform_scalar_ricci_jet_budget (M := X.manifold) C hC 6
  refine ⟨tw,htw,htwinf,hRi,lam,hlam,hnorm,hdefect,θ,hθ,N,b,hb,B,hB,?_⟩
  intro i hi p hp z hz
  obtain ⟨ht,hk,hK,hcomplete,hcurv⟩ := hjet i hi p hp z hz
  refine ⟨ht,hk,hK,hcomplete,?_⟩
  intro x hx
  exact hbudget _ hk hK x (fun j _ => hcurv j x hx)

end Yau.Proofs.C05Aux
