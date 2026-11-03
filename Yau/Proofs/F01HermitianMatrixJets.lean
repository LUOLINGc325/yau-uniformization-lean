import Yau.Proofs.F01MatrixBarJet
import Yau.Proofs.F01KahlerMixedExchange

/-! Hermitian symmetry identifies the actual barred matrix jet with the
conjugate transpose of its unbarred jet in the same coordinate direction. -/
noncomputable section
open Set Filter
open scoped Matrix Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ}

theorem matrixBarJet_eq_conjTranspose_unbar
    (H : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    {S : Set (ComplexVector n)} (hS : IsOpen S)
    (hH : ∀ w ∈ S, (H w).IsHermitian) {z : ComplexVector n} (hz : z ∈ S)
    (v : ComplexVector n) : matrixBarJet H z v = (matrixUnbarJet H z v)ᴴ := by
  ext i j
  have hgerm : (fun w => H w i j) =ᶠ[𝓝 z] (fun w => star (H w j i)) := by
    filter_upwards [hS.mem_nhds hz] with w hw
    exact (hH w hw).apply i j |>.symm
  change wirtBar (fun w => H w i j) z v = star (wirt (fun w => H w j i) z v)
  rw [wirtBar_eq_of_eventuallyEq hgerm, L14Aux.wirtBar_star]

end Yau.NodeProofs.F01Aux
