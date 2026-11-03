import Yau.Proofs.V03LeviCalculus

/-! Locality and constant cancellation at arbitrary points and directions
for the actual nested Wirtinger derivative. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem mixedWirt_congr {f g : E → ℂ} {z : E} (hfg : f =ᶠ[𝓝 z] g) (v w : E) :
    wirt (fun y => wirtBar f y v) z w = wirt (fun y => wirtBar g y v) z w := by
  have hd := hfg.fderiv (𝕜 := ℝ)
  have hb : (fun y => wirtBar f y v) =ᶠ[𝓝 z] (fun y => wirtBar g y v) :=
    hd.mono fun y hy => by simp only [wirtBar, hy]
  unfold wirt
  rw [hb.fderiv_eq]

theorem wirtBar_add_const (f : E → ℂ) (c : ℂ) (z v : E) :
    wirtBar (fun y => f y + c) z v = wirtBar f z v := by
  simp only [wirtBar, fderiv_add_const]

theorem mixedWirt_add_const (f : E → ℂ) (c : ℂ) (z v w : E) :
    wirt (fun y => wirtBar (fun y' => f y' + c) y v) z w =
      wirt (fun y => wirtBar f y v) z w := by
  simp only [wirtBar_add_const]

theorem mixedWirt_log_const_mul {f : E → ℝ} {z : E}
    (hf : ContinuousAt f z) (hs : f z ≠ 0) {c : ℝ} (hc : c ≠ 0) (v w : E) :
    wirt (fun y => wirtBar (fun y' => (Real.log (c * f y') : ℂ)) y v) z w =
      wirt (fun y => wirtBar (fun y' => (Real.log (f y') : ℂ)) y v) z w := by
  have heq : (fun y => (Real.log (c * f y) : ℂ)) =ᶠ[𝓝 z]
      (fun y => (Real.log (f y) : ℂ) + (Real.log c : ℂ)) := by
    filter_upwards [hf.eventually_ne hs] with y hy
    rw [Real.log_mul hc hy, Complex.ofReal_add, add_comm]
  rw [mixedWirt_congr heq, mixedWirt_add_const]

end Yau.Blueprint.V03Proof
