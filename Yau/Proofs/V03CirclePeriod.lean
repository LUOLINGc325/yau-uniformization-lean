import Yau.Proofs.V03LogTrace

/-! Full periodicity, including derivative periodicity later supplied by
calculus, comes from the actual circle parametrization. -/

open scoped Topology

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circlePoint_periodic : Function.Periodic circlePoint (2 * Real.pi) := by
  intro θ
  have hT := circlePoint_two_pi
  change Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 at hT
  simp only [circlePoint, Complex.ofReal_add, add_mul, Complex.exp_add, hT, mul_one]

theorem circleTrace_periodic {F : Type*} (f : ℂ → F) :
    Function.Periodic (fun θ => f (circlePoint θ)) (2 * Real.pi) := by
  intro θ
  dsimp only
  rw [circlePoint_periodic θ]

theorem logTrace_periodic {n q : ℕ} {X : KahlerManifold n}
    (d : VariationData X q) (j : ℕ) (F : VariationDisc X) :
    Function.Periodic (logTrace d j F.f) (2 * Real.pi) :=
  circleTrace_periodic (fun ζ => Real.log (wallProduct d j (F.f ζ)))

end Yau.Blueprint.V03Proof
