import Yau.Proofs.E02SchurContinuity
import Yau.Proofs.E02PSDTraceLimit
import Yau.Proofs.E02PosDefLower

open Matrix Filter Set
open scoped Topology Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem verticalBlock_sub_epsilon {n : ℕ}
    (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (ε : ℝ) :
    (W-(ε : ℂ) • 1).toBlocks₂₂ = W.toBlocks₂₂-(ε : ℂ) • (1 : Herm n) := by
  ext i j
  simp only [Matrix.toBlocks₂₂,Matrix.submatrix_apply,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.one_apply,Sum.inr.injEq] <;> rfl

/-- Epsilon is removed at one fixed matrix and one fixed time coefficient.
The later κ and contact-weight limits are not combined with this limit. -/
theorem exists_psd_majorant_remove_epsilon {n : ℕ}
    (W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (r : ℝ)
    (hC : W.toBlocks₂₂.PosDef)
    (hTests : ∀ ε : ℝ, 0 < ε → (W-(ε : ℂ) • 1).toBlocks₂₂.PosDef →
      ∃ K : Herm n, K.PosSemidef ∧
        (K-schurComplement (W-(ε : ℂ) • 1)).PosSemidef ∧
        (Matrix.trace ((W-(ε : ℂ) • 1).toBlocks₂₂ᵀ*K)).re ≤ r) :
    ∃ K : Herm n, K.PosSemidef ∧ (K-schurComplement W).PosSemidef ∧
      (Matrix.trace (W.toBlocks₂₂ᵀ*K)).re ≤ r := by
  obtain ⟨β,hβ,hLower⟩ := posDef_exists_scalar_lower W.toBlocks₂₂ hC
  obtain ⟨ε,_hAnti,hε,heps⟩ := exists_seq_strictAnti_tendsto' (show (0:ℝ) < β/4 by positivity)
  have hHalf : 0 < β/2 := by positivity
  have hUniform : ∀ j, ((W-(ε j : ℂ) • 1).toBlocks₂₂-
      ((β/2 : ℝ) : ℂ) • (1 : Herm n)).PosSemidef := by
    intro j
    have hGap : 0 ≤ β/2-ε j := by
      have hSmall : ε j < β/4 := (hε j).2
      linarith
    have hExtra : (((β/2-ε j : ℝ) : ℂ) • (1 : Herm n)).PosSemidef :=
      Matrix.PosSemidef.one.smul (RCLike.ofReal_nonneg.mpr hGap : (0:ℂ) ≤ ((β/2-ε j : ℝ) : ℂ))
    have hSum := hLower.add hExtra
    rw [verticalBlock_sub_epsilon]
    convert hSum using 1 <;> push_cast <;> module
  have hShiftPD : ∀ j, (W-(ε j : ℂ) • 1).toBlocks₂₂.PosDef := by
    intro j
    have hPos : (((β/2 : ℝ) : ℂ) • (1 : Herm n)).PosDef :=
      Matrix.PosDef.one.smul (RCLike.ofReal_pos.mpr hHalf)
    have hh := Matrix.PosDef.posSemidef_add (hUniform j) hPos
    convert hh using 1 <;> module
  choose K hK hDom hTrace using (fun j => hTests (ε j) (hε j).1 (hShiftPD j))
  have hComplex : Tendsto (fun j => (ε j : ℂ)) atTop (𝓝 (0:ℂ)) := by
    simpa only [Complex.ofReal_zero] using heps.ofReal
  have hWLim : Tendsto (fun j => W-(ε j : ℂ) • 1) atTop (𝓝 W) := by
    simpa only [zero_smul,sub_zero] using
      (tendsto_const_nhds.sub (hComplex.smul (tendsto_const_nhds (x := (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)))))
  have hVert : Continuous (fun B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ => B.toBlocks₂₂) :=
    continuous_id.matrix_submatrix Sum.inr Sum.inr
  exact exists_psd_limit_of_coercive_trace_bound
    (fun j => (W-(ε j : ℂ) • 1).toBlocks₂₂)
    (fun j => schurComplement (W-(ε j : ℂ) • 1)) K W.toBlocks₂₂
    (schurComplement W) (fun _ => r) r (β/2) r hHalf
    ((hVert.tendsto W).comp hWLim)
    ((schurComplement_continuousAt W hC).tendsto.comp hWLim)
    tendsto_const_nhds hUniform hK hDom hTrace (fun _ => le_rfl)

end Yau.NodeProofs.E02Aux
