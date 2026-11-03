import Yau.Proofs.F04PositiveEnergyScalar
import Yau.Proofs.F03ScalarL2Pairing

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.F04Proof

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The convex positive-part energy on the actual L2 pivot. -/
def positiveEnergy (f : Lp ℝ 2 μ) : ℝ := (1 / 2 : ℝ) * ‖Lp.posPart f‖ ^ 2

theorem scalarPositiveEnergy_integrable (f : Lp ℝ 2 μ) :
    Integrable (fun x => scalarPositiveEnergy (f x)) μ := by
  exact ((Lp.memLp f).pos_part.integrable_sq).const_mul (1 / 2 : ℝ)

theorem positiveEnergy_eq_integral (f : Lp ℝ 2 μ) :
    positiveEnergy f = ∫ x, scalarPositiveEnergy (f x) ∂μ := by
  rw [positiveEnergy, ← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_posPart f] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, scalarPositiveEnergy, pow_two]

theorem l2_real_norm_sq_integral (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all μ fun x => by simp [pow_two]

theorem l2_posPart_inner (f h : Lp ℝ 2 μ) :
    inner ℝ (Lp.posPart f) h = ∫ x, max (f x) 0 * h x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_posPart f] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]

/-- An actual quadratic remainder proves Frechet differentiability of the
energy, without differentiating the positive-part map on the energy space. -/
theorem positiveEnergy_remainder (f h : Lp ℝ 2 μ) :
    |positiveEnergy (f + h) - positiveEnergy f - inner ℝ (Lp.posPart f) h| ≤
      (1 / 2 : ℝ) * ‖h‖ ^ 2 := by
  have hsum : Integrable (fun x => scalarPositiveEnergy (f x + h x)) μ := by
    apply (scalarPositiveEnergy_integrable (f + h)).congr
    filter_upwards [Lp.coeFn_add f h] with x hx
    simp only [hx, Pi.add_apply]
  have hprod : Integrable (fun x => max (f x) 0 * h x) μ :=
    (Lp.memLp f).pos_part.integrable_mul (Lp.memLp h)
  let r : X → ℝ := fun x => scalarPositiveEnergy (f x + h x) -
    scalarPositiveEnergy (f x) - max (f x) 0 * h x
  have hr : Integrable r μ := (hsum.sub (scalarPositiveEnergy_integrable f)).sub hprod
  have he : positiveEnergy (f + h) - positiveEnergy f - inner ℝ (Lp.posPart f) h =
      ∫ x, r x ∂μ := by
    have he₂ := integral_sub (hsum.sub (scalarPositiveEnergy_integrable f)) hprod
    have he₃ := integral_sub hsum (scalarPositiveEnergy_integrable f)
    simp only [Pi.sub_apply] at he₂ he₃
    dsimp only [r]
    rw [positiveEnergy_eq_integral, positiveEnergy_eq_integral, l2_posPart_inner, he₂, he₃]
    congr 2
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f h] with x hx
    simp only [hx, Pi.add_apply]
  have hr0 : 0 ≤ ∫ x, r x ∂μ := integral_nonneg fun x =>
    (scalarPositiveEnergy_remainder (f x) (h x)).1
  have hb := integral_mono hr ((Lp.memLp h).integrable_sq.const_mul (1 / 2 : ℝ))
    (fun x => (scalarPositiveEnergy_remainder (f x) (h x)).2)
  rw [he, abs_of_nonneg hr0]
  simpa only [integral_const_mul, ← l2_real_norm_sq_integral] using hb

theorem positiveEnergy_hasFDerivAt (f : Lp ℝ 2 μ) :
    HasFDerivAt positiveEnergy (innerSL ℝ (Lp.posPart f)) f := by
  apply hasFDerivAt_of_quadratic_remainder positiveEnergy f (innerSL ℝ (Lp.posPart f))
    (C := (1 / 2 : ℝ)) (by norm_num)
  exact positiveEnergy_remainder f

theorem positiveEnergy_contDiff : ContDiff ℝ 1 (positiveEnergy : Lp ℝ 2 μ → ℝ) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨fun f => innerSL ℝ (Lp.posPart f),
    (innerSL ℝ).continuous.comp Lp.continuous_posPart, positiveEnergy_hasFDerivAt⟩

end Yau.F04Proof
