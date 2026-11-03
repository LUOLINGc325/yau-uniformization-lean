import Yau.Proofs.C02UniformCayleyJets
import Yau.Proofs.C02UniformFiniteJetDilation

/-! One positive dilation precedes every complex-structure field in the
bounded family and makes the prescribed finite Cayley jet uniformly small. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux
variable {n : ℕ}

theorem exists_uniform_cayley_finiteJet_dilation
    (n : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (b : ℕ → ℝ) (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 2 * r < ρ ∧
      ∀ J : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n,
      ContDiffOn ℝ ∞ J (Metric.ball 0 ρ) → J 0 = complexStructureCLM n →
      (∀ x ∈ Metric.ball (0 : ComplexVector n) ρ, ‖J x - complexStructureCLM n‖ ≤ 1 / 4) →
      (∀ m x, x ∈ Metric.ball (0 : ComplexVector n) ρ → ‖iteratedFDeriv ℝ m J x‖ ≤ b m) →
      ∀ k ≤ q, ∀ z ∈ Metric.closedBall (0 : ComplexVector n) 2,
        ‖iteratedFDeriv ℝ k (complexCayleyField (fun y => J (r • y))) z‖ ≤ ε := by
  obtain ⟨c, hc, hCayley⟩ := exists_uniform_cayley_jet_bounds n b
  obtain ⟨r, hr, hr1, hrρ, hSmall⟩ :=
    exists_uniform_finiteJet_dilation (E := ComplexVector n)
      (F := ComplexVector n →L[ℝ] ComplexVector n) ρ hρ c hc q ε hε
  refine ⟨r, hr, hr1, hrρ, ?_⟩
  intro J hJ hJ0 hClose hBound
  obtain ⟨hSmooth, hJets⟩ := hCayley (Metric.ball 0 ρ) Metric.isOpen_ball J hJ hClose hBound
  have hZero : complexCayleyField J 0 = 0 := by simp [complexCayleyField, hJ0]
  exact hSmall (complexCayleyField J) hSmooth hZero (fun k _ z hz => hJets k z hz)

end Yau.Blueprint.C02Proof
