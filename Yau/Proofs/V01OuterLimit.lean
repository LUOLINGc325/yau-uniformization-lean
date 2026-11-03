import Yau.Proofs.V01TraceCoercive
import Yau.Proofs.V01SchurContinuous
import Yau.Proofs.V01UniformPositive
import Mathlib.Analysis.SpecificLimits.Basic

/-! V01 scratch source: removing the quadratic penalty is an outer limit,
after the complete positive-majorant construction for each individual test. -/

noncomputable section
open Set Filter Matrix
open scoped Topology Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Yau.Blueprint.V01Proof

variable {n : ℕ}

theorem closed_schur_witness_of_shifted_witnesses
    (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (τ : ℝ)
    (hW : W.IsHermitian) (hC : W.toBlocks₂₂.PosDef)
    (hshift : ∀ α : ℝ, 0 < α →
      (W - (α : ℂ) • 1).toBlocks₂₂.PosDef →
      ∃ K : Herm n, K.PosSemidef ∧
        (K - schurComplement (W - (α : ℂ) • 1)).PosSemidef ∧
        ((W - (α : ℂ) • 1).toBlocks₂₂ᵀ * K).trace.re ≤ τ) :
    ∃ K : Herm n, K.PosSemidef ∧ (K - schurComplement W).PosSemidef ∧
      (W.toBlocks₂₂ᵀ * K).trace.re ≤ τ := by
  classical
  let α : ℕ → ℝ := fun m => ((m : ℝ) + 1)⁻¹
  have hα (m : ℕ) : 0 < α m := by dsimp [α]; positivity
  have hαlim : Tendsto α atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let Wm : ℕ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    fun m => W - (α m : ℂ) • 1
  have hWmlim : Tendsto Wm atTop (𝓝 W) := by
    have hcast : Tendsto (fun m => (α m : ℂ)) atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hαlim
    simpa only [zero_smul, sub_zero] using tendsto_const_nhds.sub
      (hcast.smul (tendsto_const_nhds (x := (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ))))
  let C : ℕ → Herm n := fun m => (Wm m).toBlocks₂₂
  have hClim : Tendsto C atTop (𝓝 W.toBlocks₂₂) :=
    continuous_toBlocks₂₂.continuousAt.tendsto.comp hWmlim
  have hWHerm (m : ℕ) : (Wm m).IsHermitian :=
    hW.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.of_nonneg (by
      exact_mod_cast (hα m).le)))
  have hCHerm : ∀ᶠ m in atTop, (C m).IsHermitian :=
    Eventually.of_forall (fun m => (hWHerm m).submatrix Sum.inr)
  have hCpos : ∀ᶠ m in atTop, (C m).PosDef :=
    eventually_posDef_of_tendsto C hC hClim hCHerm
  obtain ⟨c, hc, hCbound⟩ := eventually_uniform_pos_lower_bound C hC hClim hCHerm
  have hchoice (m : ℕ) : ∃ K : Herm n, (C m).PosDef →
      K.PosSemidef ∧ (K - schurComplement (Wm m)).PosSemidef ∧
        ((C m)ᵀ * K).trace.re ≤ τ := by
    by_cases hm : (C m).PosDef
    · obtain ⟨K, hK⟩ := hshift (α m) (hα m) hm
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun hp => (hm hp).elim⟩
  choose K hK using hchoice
  have hKpos : ∀ᶠ m in atTop, (K m).PosSemidef :=
    hCpos.mono (fun m hm => (hK m hm).1)
  have hKorder : ∀ᶠ m in atTop, (K m - schurComplement (Wm m)).PosSemidef :=
    hCpos.mono (fun m hm => (hK m hm).2.1)
  have hKcost : SeqUpperZero (fun m => ((C m)ᵀ * K m).trace.re - τ) := by
    intro r hr
    filter_upwards [hCpos] with m hm
    linarith [(hK m hm).2.2]
  exact closed_psd_witness_of_coercive_cost K C (fun m => schurComplement (Wm m))
    W.toBlocks₂₂ (schurComplement W) τ c hc hClim (tendsto_schurComplement hWmlim hC)
      hKpos hKorder hCbound hKcost

end Yau.Blueprint.V01Proof
