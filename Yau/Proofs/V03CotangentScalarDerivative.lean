import Yau.Proofs.V03CotangentScalarMixed

/-! First real scalar derivatives transport through the actual
holomorphic cotangent chart, in every complex parameter direction. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

theorem cotangentHolomorphicOn_scalar_fderiv {n : ℕ} {M : ComplexManifold n}
    {S : Set ℂ} {f : ℂ → CotangentPoint M} (hf : CotangentHolomorphicOn f S)
    (hS : S ∈ 𝓝 (0 : ℂ)) {b : CotangentPoint M → ℝ}
    (hb : DifferentiableAt ℝ (fun w => b (cotangentChartInv (f 0).1 w))
      (cotangentChart (f 0).1 (f 0))) (v : ℂ) :
    fderiv ℝ (fun z => b (f z)) 0 v =
      fderiv ℝ (fun w => b (cotangentChartInv (f 0).1 w))
        (cotangentChart (f 0).1 (f 0))
        (fderiv ℂ (fun z => cotangentChart (f 0).1 (f z)) 0 v) := by
  obtain ⟨V, hV, h0V, hsrc, hcoord⟩ := hf.2 0 (mem_of_mem_nhds hS)
  have hSV : S ∩ V ∈ 𝓝 (0 : ℂ) := inter_mem hS (hV.mem_nhds h0V)
  have hT : DifferentiableAt ℂ (fun z => cotangentChart (f 0).1 (f z)) 0 :=
    (hcoord.contDiffAt hSV).differentiableAt (by simp)
  have heq : (fun z => b (f z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => b (cotangentChartInv (f 0).1 (cotangentChart (f 0).1 (f z)))) := by
    filter_upwards [hSV] with z hz
    rw [cotangentChart_left_inv (f 0).1 (hsrc z hz)]
  rw [heq.fderiv_eq]
  change fderiv ℝ ((fun w => b (cotangentChartInv (f 0).1 w)) ∘
    (fun z => cotangentChart (f 0).1 (f z))) 0 v = _
  rw [fderiv_comp 0 hb (hT.restrictScalars ℝ), hT.fderiv_restrictScalars ℝ]
  rfl

end Yau.Blueprint.V03Proof
