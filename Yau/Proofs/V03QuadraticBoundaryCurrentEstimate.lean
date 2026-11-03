import Yau.Proofs.V03QuadraticBoundaryProduct

/-! A single constant before all scalar traces controls the actual
coefficient-times-two-velocity derivative current by a common native seminorm budget. -/

open scoped Topology
open MeasureTheory

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem quadraticDerivativeCurrent_uniform_bound (L M Cu CB Cv CW : ℝ)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hCW : 0 ≤ CW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ENNReal), T ≠ ⊤ → ∀ (u B v W W' : ℝ → ℂ),
      Continuous u → Continuous B → Continuous v → Continuous W' →
      Function.Periodic u (2 * Real.pi) → Function.Periodic B (2 * Real.pi) →
      Function.Periodic v (2 * Real.pi) → Function.Periodic W (2 * Real.pi) →
      Function.Periodic W' (2 * Real.pi) → (∀ θ, HasDerivAt W (W' θ) θ) →
      (∀ θ, ‖u θ‖ ≤ L) → (∀ θ, ‖B θ‖ ≤ M) → (∀ θ, ‖v θ‖ ≤ L) →
      boundaryDSq (fun θ (_ : Unit) => u θ) ≤ ENNReal.ofReal Cu * T →
      boundaryDSq (fun θ (_ : Unit) => B θ) ≤ ENNReal.ofReal CB * T →
      boundaryDSq (fun θ (_ : Unit) => v θ) ≤ ENNReal.ofReal Cv * T →
      boundaryDSq (fun θ (_ : Unit) => W θ) ≤ ENNReal.ofReal CW * T →
      |∫ θ in (-Real.pi)..Real.pi, (star (u θ) * B θ * v θ * W' θ).re| ≤ C * T.toReal := by
  let D : ENNReal := ENNReal.ofReal (2 * L ^ 2) *
      (ENNReal.ofReal (2 * M ^ 2) * ENNReal.ofReal Cu +
        ENNReal.ofReal (2 * L ^ 2) * ENNReal.ofReal CB) +
      ENNReal.ofReal (2 * (L * M) ^ 2) * ENNReal.ofReal Cv
  have hD : D ≠ ⊤ := by dsimp only [D]; finiteness
  refine ⟨Real.pi * (D.toReal + CW), mul_nonneg Real.pi_pos.le (add_nonneg ENNReal.toReal_nonneg hCW),
    fun T hT u B v W W' hu hB hv hW' hup hBp hvp hWp hW'p hd huL hBM hvL hDu hDB hDv hDW => ?_⟩
  let P : ℝ → ℂ := fun θ => star (u θ) * B θ * v θ
  have hPc : Continuous P := (hu.star.mul hB).mul hv
  have hPp : Function.Periodic P (2 * Real.pi) := by
    intro θ
    dsimp only [P]
    rw [hup θ, hBp θ, hvp θ]
  have hPD : boundaryDSq (fun θ (_ : Unit) => P θ) ≤ D * T := by
    have hh := boundaryDSq_quadratic_product_le hu hB hv hup hBp hvp hL hM huL hBM hvL
    calc
      _ ≤ ENNReal.ofReal (2 * L ^ 2) *
          (ENNReal.ofReal (2 * M ^ 2) * (ENNReal.ofReal Cu * T) +
            ENNReal.ofReal (2 * L ^ 2) * (ENNReal.ofReal CB * T)) +
          ENNReal.ofReal (2 * (L * M) ^ 2) * (ENNReal.ofReal Cv * T) := by
        apply hh.trans
        gcongr
      _ = _ := by dsimp only [D]; ring
  have hPDf : boundaryDSq (fun θ (_ : Unit) => P θ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hD hT) hPD
  have hDWf : boundaryDSq (fun θ (_ : Unit) => W θ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT) hDW
  have hPsp : Function.Periodic (fun θ => star (P θ)) (2 * Real.pi) := fun θ => congrArg star (hPp θ)
  have hPsD : boundaryDSq (fun θ (_ : Unit) => star (P θ)) =
      boundaryDSq (fun θ (_ : Unit) => P θ) := scalarDSq_conj hPc hPp
  have hh := abs_boundaryDerivativeCurrent_le hPc.star hW' hPsp hW'p hd hWp
    (by rw [hPsD]; exact hPDf) hDWf
  simp only [star_star, hPsD] at hh
  have hPr := ENNReal.toReal_mono (ENNReal.mul_ne_top hD hT) hPD
  rw [ENNReal.toReal_mul] at hPr
  have hWr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT) hDW
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCW] at hWr
  calc
    _ ≤ Real.pi * ((boundaryDSq (fun θ (_ : Unit) => P θ)).toReal +
        (boundaryDSq (fun θ (_ : Unit) => W θ)).toReal) := hh
    _ ≤ Real.pi * (D.toReal * T.toReal + CW * T.toReal) :=
      mul_le_mul_of_nonneg_left (add_le_add hPr hWr) Real.pi_pos.le
    _ = _ := by ring

end Yau.Blueprint.V03Proof
