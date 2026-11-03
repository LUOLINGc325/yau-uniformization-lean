import Yau.LeafProofs.L05PerturbationGeometry

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- The explicit two-case power bound used by the quantitative Perron barriers. -/
theorem perturb_power_barrier {z eps nu : ℝ} (hz : 0≤z) (he : 0<eps)
    (hn : 0<nu) (hn1 : nu<1) :
    z^nu ≤ eps^nu+eps^(nu-1)*z := by
  by_cases hze : z≤eps
  · have hp := Real.rpow_le_rpow hz hze hn.le
    have hq := mul_nonneg (Real.rpow_nonneg he.le (nu-1)) hz
    linarith
  · have hez : eps<z := lt_of_not_ge hze
    have ha : z^(nu-1) ≤ eps^(nu-1) :=
      Real.rpow_le_rpow_of_nonpos he hez.le (by linarith)
    have hi : z^(nu-1)*z=z^nu := by
      rw [← Real.rpow_add_one (ne_of_gt (he.trans hez))]
      congr 1
      ring
    have hh := mul_le_mul_of_nonneg_right ha hz
    rw [hi] at hh
    exact hh.trans (le_add_of_nonneg_left (Real.rpow_nonneg he.le nu))

end Yau.LeafProofs.L05Aux
