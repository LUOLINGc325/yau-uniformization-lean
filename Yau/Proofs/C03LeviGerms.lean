import Yau.LeafProofs.L22LeviCalculus

/-! The actual Levi calculator depends only on the germ of its input. -/

noncomputable section
open Filter
open scoped Topology

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs.L22Aux

variable {n : ℕ}

theorem leviC_congr_germ {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (heq : f =ᶠ[𝓝 z] g) : leviC f z = leviC g z := by
  have hcomplex : (fun w => (f w : ℂ)) =ᶠ[𝓝 z] (fun w => (g w : ℂ)) := by
    filter_upwards [heq] with w hw
    rw [hw]
  have hD := hcomplex.fderiv (𝕜 := ℝ)
  ext i j
  have hbar : (fun w => wirtBar (fun u => (f u : ℂ)) w (stdVec i)) =ᶠ[𝓝 z]
      (fun w => wirtBar (fun u => (g u : ℂ)) w (stdVec i)) := by
    filter_upwards [hD] with w hw
    simp only [wirtBar, hw]
  simp only [leviC, leviMatrix, wirt, hbar.fderiv_eq (𝕜 := ℝ)]

theorem complexLeviQuadratic_congr_germ {f g : ComplexVector n → ℝ}
    {z : ComplexVector n} (heq : f =ᶠ[𝓝 z] g) (v : ComplexVector n) :
    complexLeviQuadratic f z v = complexLeviQuadratic g z v := by
  simp only [complexLeviQuadratic, (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

end Yau.Proofs.C03Aux
