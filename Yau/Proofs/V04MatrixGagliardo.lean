import Yau.Proofs.V03GagliardoProduct
import Yau.Proofs.V03PeriodicCircle
import Yau.Proofs.V04NegativeContinuity

/-! Sum the actual normalized Gagliardo integrals before applying the
Hilbert-Schmidt contraction. No dimension factor or finite-seminorm
assumption is introduced. -/

open MeasureTheory AddCircle
open scoped Topology ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof

theorem sum_circleDirichlet_eq_lintegral {T : ℝ} [Fact (0 < T)]
    {ι : Type*} [Fintype ι] (u : AddCircle T → ι → ℂ)
    (hu : ∀ i, Continuous (fun x => u x i)) :
    ∑ i, circleDirichlet (fun x => u x i) =
      ∫⁻ p, ∑ i, circleDifferenceDensity (fun x => u x i) p
        ∂(haarAddCircle.prod haarAddCircle) := by
  rw [lintegral_finsetSum Finset.univ
    (fun i _ => circleDifferenceDensity_measurable (hu i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [← circleGagliardo_eq_dirichlet (hu i), circleGagliardo_eq_prod (hu i)]

theorem sum_circleDirichlet_le_of_square_sum_bound {T : ℝ} [Fact (0 < T)]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u : AddCircle T → ι → ℂ} {v : AddCircle T → κ → ℂ}
    (hu : ∀ i, Continuous (fun x => u x i)) (hv : ∀ k, Continuous (fun x => v x k))
    (hb : ∀ x y, ∑ k, ‖v x k - v y k‖ ^ 2 ≤ ∑ i, ‖u x i - u y i‖ ^ 2) :
    ∑ k, circleDirichlet (fun x => v x k) ≤ ∑ i, circleDirichlet (fun x => u x i) := by
  rw [sum_circleDirichlet_eq_lintegral _ hv, sum_circleDirichlet_eq_lintegral _ hu]
  apply lintegral_mono
  intro p
  unfold circleDifferenceDensity
  dsimp only
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Finset.sum_div] using
    div_le_div_of_nonneg_right (hb (p.2 + p.1) p.2) (sq_nonneg ‖fourier 1 p.1 - 1‖)

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem boundaryDSq_eq_sum_periodic_lift {ι : Type*} [Fintype ι]
    (u : ℝ → ι → ℂ) (hp : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi)) :
    boundaryDSq u = ∑ i, circleDirichlet (hp i).lift := by
  unfold boundaryDSq circleDirichlet
  apply Finset.sum_congr rfl
  intro i _
  simp only [circleFourier_eq_periodic_lift (hp i), Int.cast_abs]

theorem boundaryDSq_le_of_square_sum_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    {u : ℝ → ι → ℂ} {v : ℝ → κ → ℂ}
    (hu : ∀ i, Continuous (fun θ => u θ i)) (hv : ∀ k, Continuous (fun θ => v θ k))
    (hup : ∀ i, Function.Periodic (fun θ => u θ i) (2 * Real.pi))
    (hvp : ∀ k, Function.Periodic (fun θ => v θ k) (2 * Real.pi))
    (hb : ∀ θ t, ∑ k, ‖v θ k - v t k‖ ^ 2 ≤ ∑ i, ‖u θ i - u t i‖ ^ 2) :
    boundaryDSq v ≤ boundaryDSq u := by
  rw [boundaryDSq_eq_sum_periodic_lift _ hvp, boundaryDSq_eq_sum_periodic_lift _ hup]
  apply sum_circleDirichlet_le_of_square_sum_bound
    (fun i => periodic_lift_continuous (hup i) (hu i))
    (fun k => periodic_lift_continuous (hvp k) (hv k))
  intro x y
  induction x using Quotient.inductionOn' with
  | h θ =>
      induction y using Quotient.inductionOn' with
      | h t => exact hb θ t

variable {n : ℕ}

theorem matrixDSq_negative_le {A : ℝ → CotangentMatrix n}
    (hA : ∀ i k, Continuous (fun θ => A θ i k))
    (hAp : Function.Periodic A (2 * Real.pi)) (hHerm : ∀ θ, (A θ).IsHermitian) :
    matrixDSq (fun θ => matrixNegative (A θ)) ≤ matrixDSq A := by
  apply boundaryDSq_le_of_square_sum_bound
    (u := fun θ (p : CotangentIndex n × CotangentIndex n) => A θ p.1 p.2)
    (v := fun θ (p : CotangentIndex n × CotangentIndex n) => matrixNegative (A θ) p.1 p.2)
    (fun p => hA p.1 p.2) (fun p => matrixNegative_entry_continuous hA hHerm p.1 p.2)
    (fun p θ => congrFun (congrFun (hAp θ) p.1) p.2)
    (fun p θ => congrFun (congrFun (congrArg matrixNegative (hAp θ)) p.1) p.2)
  intro θ t
  simpa only [Fintype.sum_prod_type, Matrix.sub_apply, matrixFrobSq] using
    matrixNegative_frobSq_sub_le (A θ) (A t) (hHerm θ) (hHerm t)

end Yau.Blueprint.V04Proof
