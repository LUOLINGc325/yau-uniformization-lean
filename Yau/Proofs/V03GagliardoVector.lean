import Yau.Proofs.V03GagliardoProduct
import Yau.Proofs.V03BoundaryVectorProduct

/-! Finite-vector difference bounds control the original component-summed
Fourier seminorm. The actual ENNReal infinite endpoints are retained. -/

open scoped Topology
open MeasureTheory AddCircle

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

theorem circleDirichlet_le_of_sum_square_bound {T : ℝ} [Fact (0 < T)]
    {ι : Type*} [Fintype ι] {u : AddCircle T → ι → ℂ} {v : AddCircle T → ℂ}
    (hu : ∀ i, Continuous (fun x => u x i)) (hv : Continuous v) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x y, ‖v x - v y‖ ^ 2 ≤ C * ∑ i, ‖u x i - u y i‖ ^ 2) :
    circleDirichlet v ≤ ENNReal.ofReal C * ∑ i, circleDirichlet (fun x => u x i) := by
  rw [← circleGagliardo_eq_dirichlet hv, circleGagliardo_eq_prod hv]
  calc
    _ ≤ ∫⁻ p : AddCircle T × AddCircle T,
        ENNReal.ofReal C * ∑ i, circleDifferenceDensity (fun x => u x i) p
        ∂(haarAddCircle.prod haarAddCircle) := by
      apply lintegral_mono
      intro p
      unfold circleDifferenceDensity
      dsimp only
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity),
        ← ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have hh := div_le_div_of_nonneg_right (hb (p.2 + p.1) p.2)
        (sq_nonneg ‖fourier 1 p.1 - 1‖)
      simpa only [Finset.sum_div, mul_div_assoc] using hh
    _ = ENNReal.ofReal C * ∑ i, (∫⁻ p, circleDifferenceDensity (fun x => u x i) p
        ∂(haarAddCircle.prod haarAddCircle)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum Finset.univ (fun i _ => circleDifferenceDensity_measurable (hu i))]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← circleGagliardo_eq_prod (hu i), circleGagliardo_eq_dirichlet (hu i)]

theorem boundaryDSq_le_of_sum_square_bound {ι : Type*} [Fintype ι]
    {u : ℝ → ι → ℂ} {v : ℝ → ℂ} (hu : ∀ i, Continuous (fun θ => u θ i)) (hv : Continuous v)
    (hup : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi))
    (hvp : Function.Periodic v (2 * Real.pi)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ θ t, ‖v θ - v t‖ ^ 2 ≤ C * ∑ i, ‖u θ i - u t i‖ ^ 2) :
    boundaryDSq (fun θ (_ : Unit) => v θ) ≤ ENNReal.ofReal C * boundaryDSq u := by
  letI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  have hsum : boundaryDSq u = ∑ i, circleDirichlet (hup i).lift := by
    rw [boundaryDSq_eq_sum_singleton]
    apply Finset.sum_congr rfl
    intro i _
    exact circleDirichlet_periodic_lift (hup i)
  rw [hsum, circleDirichlet_periodic_lift hvp]
  apply circleDirichlet_le_of_sum_square_bound
    (fun i => periodic_lift_continuous (hup i) (hu i)) (periodic_lift_continuous hvp hv) hC
  intro x y
  induction x using Quotient.inductionOn' with
  | h θ =>
      induction y using Quotient.inductionOn' with
      | h t => exact hb θ t

end Yau.Blueprint.V03Proof
