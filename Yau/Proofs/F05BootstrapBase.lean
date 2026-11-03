import Yau.Proofs.F05BootstrapRestrictions
import Yau.Proofs.F05BootstrapLowInterpolation

/-! The supplied native Schauder solution starts the relative bootstrap.
Its missing lower-jet Hölder estimate is obtained by proved inward secants,
including at the actual physical face and terminal time. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_native_schauder_local_relative (ν : Option (RIdx n)) {T α K : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {v : Point n → ℝ}
    (hv : SchauderBound α (cylinder (region ν 2) 0 T) v K) :
    F05LocalSchauder α ν T v := by
  intro r hr hr2 s hs hsT
  let ρ : ℝ := min 1 ((2-r)/2)
  have hρ : 0 < ρ := lt_min (by norm_num) (by linarith)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hMargin : r+ρ ≤ 2 := by have h := min_le_right (1 : ℝ) ((2-r)/2); linarith
  have hK : 0 ≤ K := hv.2.1
  have hInterval := F05_schauder_restrict_interval hsT hs.le le_rfl hv
  have hBig : F05RelC2 (region ν 2) (Icc s T) v :=
    F05_native_c2_to_relative (F05_region_uniqueDiffOn ν (by norm_num)) hInterval.1
  have hRaw : ∀ z ∈ region ν 2 ×ˢ Icc s T,
      ‖F05RelDD (region ν 2) v z‖ ≤ K ∧ |F05RelT (Icc s T) v z| ≤ K := by
    intro z hz
    rw [F05RelDD_eq_spatialDD (F05_region_uniqueDiffOn ν (by norm_num)) hz.1
      (fun x hx => hInterval.1.2.2.2.2.1 (x,z.2) ⟨hx,hz.2⟩),
      F05RelT_eq_timeD v hz.1]
    exact ⟨hInterval.2.2.2.1.2.1 z hz,hInterval.2.2.2.2.2.1 z hz⟩
  have hLow := F05_relative_cap_low_interpolation ν hα hα1 (by norm_num)
    hρ hρ1 hMargin hK hK hBig (fun z hz => (hInterval.2.2.1 z hz).1) hRaw
  have hHigh := F05_native_local_relative_high ν hv hr hr2 hs.le hsT
  let L : ℝ := 8*(ρ^(1-α)*K+ρ^(-1-α)*K)
  have hL : 0 ≤ L := hLow.1
  refine ⟨1+K+L,by linarith,hHigh.1,?_,?_,?_⟩
  · apply holderBound_mono_const _ (show L ≤ 1+K+L by linarith)
    apply holderBound_congr_on hLow
    intro z hz
    change (v z,F05RelD (region ν 2) v z) = (v z,F05RelD (region ν r) v z)
    congr 1
    rw [F05RelD_eq_spatialD (F05_region_uniqueDiffOn ν (by norm_num) z.1
      (F05_region_mono hr2.le hz.1))
      ((hInterval.1.2.2.2.2.1 z ⟨F05_region_mono hr2.le hz.1,hz.2⟩).differentiableAt
        (by norm_num)),
      F05RelD_eq_spatialD (F05_region_uniqueDiffOn ν hr z.1 hz.1)
      ((hInterval.1.2.2.2.2.1 z ⟨F05_region_mono hr2.le hz.1,hz.2⟩).differentiableAt
        (by norm_num))]
  · exact holderBound_mono_const hHigh.2.2.1 (by linarith)
  · exact holderBound_mono_const hHigh.2.2.2 (by linarith)

end Yau.Proofs.F05Aux
