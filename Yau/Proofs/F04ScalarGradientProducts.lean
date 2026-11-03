import Yau.Proofs.F04AdjointGlobal

open MeasureTheory Filter
open scoped Topology ContDiff Manifold

noncomputable section

namespace Yau.F04Proof

open Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem scalarGradientPair_product_left (h : HermitianField M)
    {a f : M.Carrier → ℝ} (ha : SmoothFn a) (hf : SmoothFn f)
    (k : M.Carrier → ℝ) (x : M.Carrier) :
    scalarGradientPair h (fun y => a y * f y) k x =
      a x * scalarGradientPair h f k x + f x * scalarGradientPair h a k x := by
  have hp := chartGradientPair_mul_left h x (inChart x k)
    ((contDiffAt_inChart ha x (mem_extChartAt_target x)).differentiableAt (by simp))
    ((contDiffAt_inChart hf x (mem_extChartAt_target x)).differentiableAt (by simp))
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  change scalarGradientPair h (fun y => a y * f y) k x =
    a (chartInv x (chartPt x x)) * scalarGradientPair h f k x +
      f (chartInv x (chartPt x x)) * scalarGradientPair h a k x at hp
  simpa only [hx] using hp

/-- The density exactly cancels the exponential test multiplier, including
its genuine first order drift term. -/
theorem scalarGradientPair_exponential_density (h : HermitianField M)
    {ρ v : M.Carrier → ℝ} (hρ : SmoothFn ρ) (hv : SmoothFn v)
    (u : M.Carrier → ℝ) (x : M.Carrier) :
    Real.exp (-ρ x) * scalarGradientPair h (fun y => Real.exp (ρ y) * v y) u x =
      scalarGradientPair h v u x + v x * scalarGradientPair h ρ u x := by
  have he : SmoothFn (fun y => Real.exp (ρ y)) := fun c => (hρ c).exp
  rw [scalarGradientPair_product_left h he hv]
  rw [scalarGradientPair_scalar_comp_left h hρ u Real.exp x (Real.differentiable_exp _)]
  simp only [Real.deriv_exp]
  have hc : Real.exp (-ρ x) * Real.exp (ρ x) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc
    _ = (Real.exp (-ρ x) * Real.exp (ρ x)) *
        (scalarGradientPair h v u x + v x * scalarGradientPair h ρ u x) := by ring
    _ = _ := by rw [hc, one_mul]

end Yau.F04Proof
