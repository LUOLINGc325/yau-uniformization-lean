import Yau.Proofs.C04ClockBasic

/-! The same clock controls logarithmic physical-time intervals. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter Set

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem clock_logarithmic_interval (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {u t : ℝ} (hu : 0 < u) (hut : u ≤ t) :
    clockSpeed o h u * (Real.log t - Real.log u) ≤ ρ o t - ρ o u := by
  let q := clockSpeed o h
  have hmono : MonotoneOn (fun v => ρ o v - q u * Real.log v) (Ici u) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici u)
    · intro v hv
      exact ((rho_hasDerivAt X o h U P ρ hf o (hu.trans_le hv)).continuousAt.sub
        ((Real.continuousAt_log (hu.trans_le hv).ne').const_mul (q u))).continuousWithinAt
    · intro v hv
      have huv : u ≤ v := interior_subset hv
      exact ((rho_hasDerivAt X o h U P ρ hf o (hu.trans_le huv)).sub
        ((Real.hasDerivAt_log (hu.trans_le huv).ne').const_mul (q u))).hasDerivWithinAt
    · intro v hv
      have huv : u ≤ v := interior_subset hv
      have hvpos : 0 < v := hu.trans_le huv
      have hq : q u ≤ q v := clockSpeed_monotoneOn X o h U P ρ hf hH hu (le_refl u) huv huv
      apply (mul_nonneg_iff_of_pos_right hvpos).mp
      dsimp only [q, clockSpeed] at *
      simp only [sub_mul, mul_assoc, inv_mul_cancel₀ hvpos.ne', mul_one]
      nlinarith
  have hh := hmono (le_refl u) hut hut
  dsimp only [q] at hh
  nlinarith

/-- A positive logarithmic secant and the clock interval estimate give the
uniform endpoint rate, without choosing or normalizing a vector. -/
theorem endpoint_rate_lower (b s q d gap L : ℝ) (hs : 0 < s) (hq : 0 < q)
    (hd : 0 ≤ d) (hlower : b * s ≤ L) (hsecant : L ≤ d * gap)
    (hclock : q * gap ≤ s) : b * q ≤ d := by
  have h₁ := mul_le_mul_of_nonneg_left hlower hq.le
  have h₂ := mul_le_mul_of_nonneg_left hsecant hq.le
  have h₃ := mul_le_mul_of_nonneg_left hclock hd
  apply (mul_le_mul_iff_right₀ hs).mp
  nlinarith

end Yau.Proofs.C04Aux
