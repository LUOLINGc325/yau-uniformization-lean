import Yau.Proofs.F05BootstrapRegions

/-! Every individual relative-C2 solution has a finite raw high-jet bound
on a compact physical cap. This supplies the starting bound for radius
absorption; its value need not be uniform in a difference-quotient step. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_relative_cap_raw_high_bound (ν : Option (RIdx n)) {r s T : ℝ}
    {v : Point n → ℝ} (hv : F05RelC2 (region ν r) (Icc s T) v) :
    ∃ K : ℝ, 0 < K ∧ ∀ z ∈ region ν r ×ˢ Icc s T,
      ‖F05RelDD (region ν r) v z‖ ≤ K ∧ |F05RelT (Icc s T) v z| ≤ K := by
  have hCompact := (F05_region_isCompact ν r).prod (isCompact_Icc (a := s) (b := T))
  obtain ⟨B,hB⟩ := hCompact.exists_bound_of_continuousOn
    (f := F05RelDD (region ν r) v) hv.2.2.1
  obtain ⟨C,hC⟩ := hCompact.exists_bound_of_continuousOn
    (f := F05RelT (Icc s T) v) hv.2.2.2.1
  refine ⟨1+|B|+|C|,by positivity,?_⟩
  intro z hz
  refine ⟨(hB z hz).trans (by linarith [le_abs_self B,abs_nonneg C]),?_⟩
  have hTime : |F05RelT (Icc s T) v z| ≤ C := hC z hz
  exact hTime.trans (by linarith [le_abs_self C,abs_nonneg B])

end Yau.Proofs.F05Aux
