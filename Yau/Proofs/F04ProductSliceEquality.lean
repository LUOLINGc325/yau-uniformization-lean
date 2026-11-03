import Yau.LeafProofs.L19HeatRegularityJoint

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace Yau.F04Proof

/-- Actual product-L2 functions whose spatial slices agree for almost
 every time agree in product measure. Fubini is applied to the genuine
 integrable squared difference, so no global measurable evaluation of L2
 classes is postulated. -/
theorem product_memLp_ae_eq_of_ae_time_slices
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f g : α × β → ℝ} (hf : MemLp f 2 (μ.prod ν)) (hg : MemLp g 2 (μ.prod ν))
    (hSlices : ∀ᵐ t ∂ν, (fun x => f (x, t)) =ᵐ[μ] (fun x => g (x, t))) :
    f =ᵐ[μ.prod ν] g := by
  have hsq := (hf.sub hg).integrable_sq
  change Integrable (fun p => (f p - g p) ^ 2) (μ.prod ν) at hsq
  have hZero : (∫ p, (f p - g p) ^ 2 ∂μ.prod ν) = 0 := by
    rw [integral_prod_symm _ hsq]
    calc
      _ = ∫ _t, (0 : ℝ) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hSlices] with t ht
        calc
          _ = ∫ _x, (0 : ℝ) ∂μ := by
            apply integral_congr_ae
            filter_upwards [ht] with x hx
            rw [hx, sub_self, zero_pow (by decide : 2 ≠ 0)]
          _ = 0 := integral_zero _ _
      _ = 0 := integral_zero _ _
  have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun p => sq_nonneg (f p - g p))) hsq).mp hZero
  filter_upwards [hz] with p hp
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hp)

end Yau.F04Proof
