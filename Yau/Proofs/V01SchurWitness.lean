import Yau.Proofs.V01TraceCoercive
import Yau.Proofs.V01SchurContinuous
import Yau.Proofs.V01UniformPositive

/-! V01 scratch source: the complete finite-dimensional Schur closing step.
The sole named-parent input is the original `SymplecticSchur n` proposition. -/

noncomputable section
open Set Filter Matrix
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

theorem schur_witness_of_positive_majorants
    (hSchur : SymplecticSchur n)
    (A W : ℕ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (W₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (τ : ℝ)
    (hWlim : Tendsto W atTop (𝓝 W₀)) (hC₀ : W₀.toBlocks₂₂.PosDef)
    (hmajorant : ∀ᶠ m in atTop, (A m).PosDef ∧ (W m).IsHermitian ∧
      (A m - W m).PosSemidef ∧ (W m).toBlocks₂₂.PosDef)
    (hcost : SeqUpperZero (fun m => symplecticP (A m) - τ)) :
    ∃ K : Herm n, K.PosSemidef ∧ (K - schurComplement W₀).PosSemidef ∧
      (W₀.toBlocks₂₂ᵀ * K).trace.re ≤ τ := by
  let S : ℕ → Herm n := fun m => schurComplement (A m)
  let C : ℕ → Herm n := fun m => (W m).toBlocks₂₂
  let B : ℕ → Herm n := fun m => schurComplement (W m)
  have hClim : Tendsto C atTop (𝓝 W₀.toBlocks₂₂) :=
    continuous_toBlocks₂₂.continuousAt.tendsto.comp hWlim
  have hBlim : Tendsto B atTop (𝓝 (schurComplement W₀)) :=
    tendsto_schurComplement hWlim hC₀
  have hCHerm : ∀ᶠ m in atTop, (C m).IsHermitian := by
    filter_upwards [hmajorant] with m hm
    exact hm.2.2.2.isHermitian
  obtain ⟨c, hc, hCbound⟩ := eventually_uniform_pos_lower_bound C hC₀ hClim hCHerm
  have hSall : ∀ᶠ m in atTop,
      (S m).PosSemidef ∧ (S m - B m).PosSemidef ∧
        ((C m)ᵀ * S m).trace.re ≤ symplecticP (A m) := by
    filter_upwards [hmajorant] with m hm
    exact hSchur (A m) (W m) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  have hS : ∀ᶠ m in atTop, (S m).PosSemidef := hSall.mono (fun _ hm => hm.1)
  have hSB : ∀ᶠ m in atTop, (S m - B m).PosSemidef :=
    hSall.mono (fun _ hm => hm.2.1)
  have hSupper : SeqUpperZero (fun m => ((C m)ᵀ * S m).trace.re - τ) := by
    intro r hr
    filter_upwards [hSall, hcost r hr] with m hm hmr
    linarith [hm.2.2]
  exact closed_psd_witness_of_coercive_cost S C B W₀.toBlocks₂₂
    (schurComplement W₀) τ c hc hClim hBlim hS hSB hCbound hSupper

end Yau.Blueprint.V01Proof
