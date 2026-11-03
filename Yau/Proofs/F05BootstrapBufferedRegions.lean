import Yau.Proofs.F05BootstrapRegions
import Yau.LeafProofs.L16LocalCutoffBudgets

/-! Nested physical caps with independent spatial and temporal buffers.
Only their radii change during absorption; the physical side stays fixed. -/

open Set
noncomputable section
set_option maxHeartbeats 1200000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05NestedCap (ν : Option (RIdx n)) (r0 ε τ T κ : ℝ) : Set (Point n) :=
  region ν (r0+ε*κ) ×ˢ Icc (τ-ε^2*κ^2) T

theorem F05_nested_cap_mono {ν : Option (RIdx n)} {r0 ε τ T r R : ℝ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (hrR : r ≤ R) :
    F05NestedCap ν r0 ε τ T r ⊆ F05NestedCap ν r0 ε τ T R := by
  intro z hz
  refine ⟨F05_region_mono (by nlinarith) hz.1,?_,hz.2.2⟩
  have hSq := pow_le_pow_left₀ hr hrR 2
  have hMul := mul_le_mul_of_nonneg_left hSq (sq_nonneg ε)
  linarith [hz.2.1]

theorem F05_nested_cap_subset {ν : Option (RIdx n)} {r0 ε τ T s0 r Rbase : ℝ}
    (hε : 0 ≤ ε) (hr : 0 ≤ r) (hrMax : r ≤ 3/2)
    (hRadius : r0+ε*(3/2) ≤ Rbase) (hStart : s0 ≤ τ-ε^2*(3/2)^2) :
    F05NestedCap ν r0 ε τ T r ⊆ region ν Rbase ×ˢ Icc s0 T := by
  intro z hz
  have hLarger := F05_nested_cap_mono hε hr hrMax hz
  exact ⟨F05_region_mono hRadius hLarger.1,hStart.trans hLarger.2.1,hLarger.2.2⟩

theorem F05_nested_cap_patch_time_gap {δ ε r R : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε)
    (hr : 1 ≤ r) (hrR : r < R) (hR : R ≤ 3/2) :
    localSchauderTime δ (ε*(R-r)) ≤ ε^2*(R^2-r^2) := by
  let d := R-r
  have hd : 0 ≤ d := sub_nonneg.mpr hrR.le
  have hd1 : d ≤ 1 := by dsimp only [d]; linarith
  have hSquare : d^2/8 ≤ 2*d := by nlinarith
  have hSum : 2 ≤ R+r := by linarith
  have hScale := mul_le_mul_of_nonneg_left hSum hd
  have hDifference : R^2-r^2 = d*(R+r) := by dsimp only [d]; ring
  have hArithmetic : d^2/8 ≤ R^2-r^2 := by rw [hDifference]; nlinarith [hScale]
  have hDelta : δ*(d^2/8) ≤ d^2/8 := mul_le_of_le_one_left (by positivity) hδ1
  calc
    _ = ε^2*(δ*(d^2/8)) := by dsimp only [localSchauderTime,d]; ring
    _ ≤ ε^2*(d^2/8) := mul_le_mul_of_nonneg_left hDelta (sq_nonneg ε)
    _ ≤ _ := mul_le_mul_of_nonneg_left hArithmetic (sq_nonneg ε)

theorem F05_buffered_radius_inverse_power (r0 ε r R : ℝ) (P : ℕ) :
    (((r0+ε*R)-(r0+ε*r))⁻¹)^P = (ε⁻¹)^P*((R-r)⁻¹)^P := by
  rw [show (r0+ε*R)-(r0+ε*r) = ε*(R-r) by ring,mul_inv_rev,mul_pow]
  ring

end Yau.Proofs.F05Aux
