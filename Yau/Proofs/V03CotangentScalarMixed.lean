import Yau.Proofs.V03FirstField
import Yau.Proofs.V03LeviNaturality

/-! Actual mixed scalar variation in the native cotangent atlas. The
holomorphic chain rule cancels all parameter acceleration. -/

open scoped Manifold Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem cotangentHolomorphicOn_scalar_mixed {n : ℕ} {M : ComplexManifold n}
    {S : Set ℂ} {f : ℂ → CotangentPoint M} (hf : CotangentHolomorphicOn f S)
    (hS : S ∈ 𝓝 (0 : ℂ)) {b : CotangentPoint M → ℝ}
    (hb : ContDiffAt ℝ 2 (fun w => b (cotangentChartInv (f 0).1 w))
      (cotangentChart (f 0).1 (f 0))) :
    mixedReal (fun z => b (f z)) =
      (wirt (fun y => wirtBar (fun y' => (b (cotangentChartInv (f 0).1 y') : ℂ)) y
        (fderiv ℂ (fun z => cotangentChart (f 0).1 (f z)) 0 1))
        (cotangentChart (f 0).1 (f 0))
        (fderiv ℂ (fun z => cotangentChart (f 0).1 (f z)) 0 1)).re := by
  obtain ⟨V, hV, h0V, hsrc, hcoord⟩ := hf.2 0 (mem_of_mem_nhds hS)
  have hSV : S ∩ V ∈ 𝓝 (0 : ℂ) := inter_mem hS (hV.mem_nhds h0V)
  have hT : ContDiffAt ℂ 2 (fun z => cotangentChart (f 0).1 (f z)) 0 :=
    (hcoord.contDiffAt hSV).of_le (by simp)
  have heq : (fun z => b (f z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => b (cotangentChartInv (f 0).1 (cotangentChart (f 0).1 (f z)))) := by
    filter_upwards [hSV] with z hz
    rw [cotangentChart_left_inv (f 0).1 (hsrc z hz)]
  rw [mixedReal_congr heq]
  exact mixedWirt_holomorphic_comp_re hT hb 1

end Yau.Blueprint.V03Proof
