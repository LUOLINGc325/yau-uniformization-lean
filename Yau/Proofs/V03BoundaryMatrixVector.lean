import Yau.Proofs.V03MatrixBoundaryEntryProduct

/-! Actual rectangular matrix-vector products obey a finite-component
half-order Fourier bound. Empty index sets remain part of the statement. -/

open scoped Topology Matrix

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem boundaryDSq_component_le {ι : Type*} [Fintype ι]
    (u : ℝ → ι → ℂ) (i : ι) : boundaryDSq (fun θ (_ : Unit) => u θ i) ≤ boundaryDSq u := by
  classical
  simp only [boundaryDSq, Finset.univ_unique, Finset.sum_singleton]
  exact Finset.single_le_sum
    (f := fun i : ι => ∑' k : ℤ, ENNReal.ofReal ((|k| : ℤ) * ‖circleFourier (fun θ => u θ i) k‖ ^ 2))
    (s := Finset.univ) (a := i) (fun _ _ => bot_le) (Finset.mem_univ _)

theorem boundaryDSq_matrix_mulVec_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {U : ℝ → Matrix κ ι ℂ} {l : ℝ → ι → ℂ}
    (hU : ∀ b i, Continuous (fun θ => U θ b i)) (hl : ∀ i, Continuous (fun θ => l θ i))
    (hUp : ∀ b i, Function.Periodic (fun θ => U θ b i) (2 * Real.pi))
    (hlp : ∀ i, Function.Periodic (fun θ => l θ i) (2 * Real.pi))
    {L : ℝ} (hL : 0 ≤ L) (hU1 : ∀ θ b i, ‖U θ b i‖ ≤ 1) (hlL : ∀ θ i, ‖l θ i‖ ≤ L) :
    boundaryDSq (fun θ => U θ *ᵥ l θ) ≤
      (Fintype.card κ : ENNReal) * (Fintype.card ι : ENNReal) ^ 2 *
        (ENNReal.ofReal (2 * L ^ 2) * matrixDSq U + 2 * boundaryDSq l) := by
  classical
  have hprod (b : κ) (i : ι) :
      boundaryDSq (fun θ (_ : Unit) => U θ b i * l θ i) ≤
        ENNReal.ofReal (2 * L ^ 2) * matrixDSq U + 2 * boundaryDSq l := by
    have hh := boundaryDSq_mul_le (hU b i) (hl i) (hUp b i) (hlp i)
      (by norm_num : (0 : ℝ) ≤ 1) hL (fun θ => hU1 θ b i) (fun θ => hlL θ i)
    norm_num only [one_pow, mul_one, ENNReal.ofReal_ofNat] at hh
    apply hh.trans
    gcongr
    · exact matrixDSq_entry_le U b i
    · exact boundaryDSq_component_le l i
  have hentry (b : κ) : boundaryDSq (fun θ (_ : Unit) => (U θ *ᵥ l θ) b) ≤
      (Fintype.card ι : ENNReal) ^ 2 *
        (ENNReal.ofReal (2 * L ^ 2) * matrixDSq U + 2 * boundaryDSq l) := by
    change boundaryDSq (fun θ (_ : Unit) => ∑ i, U θ b i * l θ i) ≤ _
    calc
      _ ≤ (Fintype.card ι : ENNReal) * ∑ i, boundaryDSq (fun θ (_ : Unit) => U θ b i * l θ i) :=
        boundaryDSq_sum_le (fun i => (hU b i).mul (hl i)) (fun i => (hUp b i).mul (hlp i))
      _ ≤ (Fintype.card ι : ENNReal) * ∑ _i : ι,
          (ENNReal.ofReal (2 * L ^ 2) * matrixDSq U + 2 * boundaryDSq l) := by
        gcongr with i
        exact hprod b i
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  rw [boundaryDSq_eq_sum_singleton (fun θ => U θ *ᵥ l θ)]
  calc
    _ ≤ ∑ _b : κ, (Fintype.card ι : ENNReal) ^ 2 *
        (ENNReal.ofReal (2 * L ^ 2) * matrixDSq U + 2 * boundaryDSq l) :=
      Finset.sum_le_sum (fun b _ => hentry b)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end Yau.Blueprint.V03Proof
