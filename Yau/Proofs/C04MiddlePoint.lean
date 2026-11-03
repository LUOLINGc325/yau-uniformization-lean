import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! The logarithmic derivative point selected in the middle of a good window. -/

noncomputable section
open Filter Set
open scoped Topology

namespace Yau.Proofs.C04Aux

/-- Cauchy's mean value theorem uses the physical time directly, so the
quotient here is exactly the one in the original RicciWindows contract. -/
theorem exists_log_deriv_ratio_point {s q r : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hs : ContinuousOn s (Icc a b))
    (hq : ContinuousOn q (Icc a b)) (hqpos : ∀ t ∈ Icc a b, 0 < q t)
    (hsd : ∀ t ∈ Ioo a b, HasDerivAt s (r t) t)
    (hqd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ q t)
    (hrpos : ∀ t ∈ Ioo a b, 0 < r t) (hsab : s a < s b) :
    ∃ t ∈ Ioo a b, deriv q t / (q t * r t) =
      (Real.log (q b) - Real.log (q a)) / (s b - s a) := by
  have hlog : ContinuousOn (fun t => Real.log (q t)) (Icc a b) :=
    hq.log (fun t ht => (hqpos t ht).ne')
  obtain ⟨t, ht, heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    (fun t => Real.log (q t)) (fun t => deriv q t / q t) hab hlog
    (fun t ht => (hqd t ht).hasDerivAt.log (hqpos t (Ioo_subset_Icc_self ht)).ne')
    s r hs hsd
  refine ⟨t, ht, ?_⟩
  have hqne := (hqpos t (Ioo_subset_Icc_self ht)).ne'
  have hrne := (hrpos t ht).ne'
  have hsne := (sub_pos.mpr hsab).ne'
  field_simp at heq ⊢
  nlinarith

end Yau.Proofs.C04Aux
