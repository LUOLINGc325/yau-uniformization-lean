import Yau.Proofs.V01OrderedSelection
import Yau.Proofs.V01SchurWitness
import Yau.Proofs.V01CostErrors
import Mathlib.Analysis.SpecificLimits.Basic

/-! Only the Schur complements enter compactness. The positive majorants
are selected from the complete inner approximation in its original order. -/

noncomputable section
open Set Filter Matrix
open scoped Topology Matrix ComplexOrder MatrixOrder
namespace Yau.Blueprint.V01Proof
variable {n : ℕ}

theorem schur_witness_of_ordered_majorants
    (hSchur : SymplecticSchur n) (W : CotangentMatrix n) (τ : ℝ)
    (hW : W.IsHermitian) (hC : W.toBlocks₂₂.PosDef)
    (hApprox : ∀ β : ℝ, 0 < β →
      ∀ᶠ (j : ℕ) in atTop, ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ (ν : ℕ) in atTop,
          ∃ A : CotangentMatrix n, A.PosDef ∧ (A - W).PosSemidef ∧
            symplecticP A ≤ τ + β) :
    ∃ K : Herm n, K.PosSemidef ∧ (K - schurComplement W).PosSemidef ∧
      (W.toBlocks₂₂ᵀ * K).trace.re ≤ τ := by
  classical
  let β : ℕ → ℝ := fun m => ((m : ℝ) + 1)⁻¹
  have hβ (m : ℕ) : 0 < β m := by dsimp [β]; positivity
  have hChoice (m : ℕ) : ∃ A : CotangentMatrix n,
      A.PosDef ∧ (A - W).PosSemidef ∧ symplecticP A ≤ τ + β m := by
    obtain ⟨j, δ, ε, ν, _hj, _hδ, _hδsmall, _hε, _hεsmall, _hν, hA⟩ :=
      ordered_pick (hApprox (β m) (hβ m)) m (β m) (β m) (hβ m) (hβ m)
    exact hA
  choose A hA using hChoice
  have hβlim : Tendsto β atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hCost : SeqUpperZero (fun m => symplecticP (A m) - τ) :=
    seqUpperZero_of_vanishing_upper hβlim
      (Eventually.of_forall (fun m => by linarith [(hA m).2.2]))
  exact schur_witness_of_positive_majorants hSchur A (fun _ => W) W τ
    tendsto_const_nhds hC
    (Eventually.of_forall (fun m => ⟨(hA m).1, hW, (hA m).2.1, hC⟩)) hCost

end Yau.Blueprint.V01Proof
