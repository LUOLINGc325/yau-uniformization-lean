import Yau.Proofs.V04MatrixGagliardo
import Yau.Proofs.D06CircleDifferences

/-! The same native normalized Haar-circle differences used by D06
control the original component-summed Fourier seminorm. Infinite values
and the actual zero denominator are retained throughout. -/

open MeasureTheory AddCircle
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint Yau.Blueprint.V03Proof Yau.NodeProofs.D06Aux

variable {r : ℕ}

def factorCircleDirichlet (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ) : ENNReal :=
  ∑ i, ∑ j, circleDirichlet (fun t => A t i j)

theorem factorCircleDirichlet_eq_difference
    (A : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (hA : Continuous A) :
    factorCircleDirichlet A = ∫⁻ θ : HardyCircle,
      ENNReal.ofReal (circleDifference A θ / ‖fourier 1 θ - 1‖ ^ 2) ∂hardyCircleMeasure := by
  let u := fun t (p : Fin r × Fin r) => A t p.1 p.2
  have hu (p : Fin r × Fin r) : Continuous (fun t => u t p) := hA.matrix_elem p.1 p.2
  have hmeas : Measurable (fun p : HardyCircle × HardyCircle =>
      ∑ q : Fin r × Fin r, circleDifferenceDensity (fun t => u t q) p) :=
    Finset.measurable_fun_sum _ (fun q _ => circleDifferenceDensity_measurable (hu q))
  calc
    factorCircleDirichlet A = ∫⁻ p : HardyCircle × HardyCircle,
        ∑ q : Fin r × Fin r, circleDifferenceDensity (fun t => u t q) p
          ∂(hardyCircleMeasure.prod hardyCircleMeasure) := by
      simpa only [factorCircleDirichlet, Fintype.sum_prod_type, u] using
        sum_circleDirichlet_eq_lintegral u hu
    _ = ∫⁻ θ : HardyCircle, ∫⁻ t : HardyCircle,
        ENNReal.ofReal (frobSq (A (t + θ) - A t) / ‖fourier 1 θ - 1‖ ^ 2)
          ∂hardyCircleMeasure ∂hardyCircleMeasure := by
      rw [lintegral_prod _ hmeas.aemeasurable]
      apply lintegral_congr
      intro θ
      apply lintegral_congr
      intro t
      unfold circleDifferenceDensity
      dsimp only
      rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => by positivity)]
      congr 1
      simp only [u, Finset.sum_div, Fintype.sum_prod_type, frobSq, Matrix.sub_apply]
    _ = _ := by
      apply lintegral_congr
      intro θ
      have hc : Continuous (fun t : HardyCircle =>
          frobSq (A (t + θ) - A t) / ‖fourier 1 θ - 1‖ ^ 2) := by
        unfold frobSq
        fun_prop
      have hi : Integrable (fun t : HardyCircle =>
          frobSq (A (t + θ) - A t) / ‖fourier 1 θ - 1‖ ^ 2) hardyCircleMeasure :=
        hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ (fun _ => div_nonneg (frobSq_nonneg _) (sq_nonneg _))), integral_div]
      rfl

theorem factorCircleDirichlet_le_of_difference_bound
    (A B : HardyCircle → Matrix (Fin r) (Fin r) ℂ) (hA : Continuous A) (hB : Continuous B)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ θ, circleDifference A θ ≤ C * circleDifference B θ) :
    factorCircleDirichlet A ≤ ENNReal.ofReal C * factorCircleDirichlet B := by
  rw [factorCircleDirichlet_eq_difference A hA, factorCircleDirichlet_eq_difference B hB]
  calc
    _ ≤ ∫⁻ θ : HardyCircle, ENNReal.ofReal C *
        ENNReal.ofReal (circleDifference B θ / ‖fourier 1 θ - 1‖ ^ 2) ∂hardyCircleMeasure := by
      apply lintegral_mono
      intro θ
      dsimp only
      rw [← ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (hbound θ) (sq_nonneg ‖fourier 1 θ - 1‖)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Yau.Blueprint.V04Proof
