import Yau.Proofs.P04RadialGradient
import Yau.Proofs.P04RankOneBound
import Yau.Proofs.P04LogLeviPositivity

noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.Proofs.P04Aux
open Yau
variable {n : ℕ}

/-- The genuine regularized logarithmic pole is plurisubharmonic, computed
using the original real-Fréchet Wirtinger calculator. -/
theorem leviC_log_poleQuadratic_posSemidef (z₀ : ComplexVector n) {ε : ℝ}
    (hε : 0 < ε) (z : ComplexVector n) :
    (leviC (fun y => Real.log (poleQuadratic z₀ ε y)) z).PosSemidef := by
  have hpos : 0 < poleQuadratic z₀ ε z := by unfold poleQuadratic; positivity
  apply leviC_log_posSemidef_of_numerator
    ((poleQuadratic_smooth z₀ ε).contDiffAt.of_le (by simp)) hpos
  rw [leviC_poleQuadratic,gradientGram_poleQuadratic]
  have H := (radial_cauchy_matrix (z-z₀)).add
    ((Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℂ).PosSemidef).smul (sq_nonneg ε))
  convert H using 1
  ext i j
  change (poleQuadratic z₀ ε z : ℂ)*(1 : Matrix (Fin n) (Fin n) ℂ) i j -
      (z-z₀) i*star ((z-z₀) j) =
    (((‖z-z₀‖^2 : ℝ) : ℂ)*(1 : Matrix (Fin n) (Fin n) ℂ) i j -
      (z-z₀) i*star ((z-z₀) j)) + (ε^2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) i j
  simp only [poleQuadratic,Complex.ofReal_add,Complex.real_smul]
  push_cast
  ring

end Yau.Proofs.P04Aux
