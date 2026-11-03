import Yau.Proofs.C01ScalarPathJets

/-! A genuine change of time along a path of continuous nonnegative
speed.  It works also for constant paths and zero scalar curvature. -/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff

namespace Yau.NodeProofs.C01Aux

def speedPrimitive (v : ℝ → ℝ) (s : ℝ) : ℝ := ∫ u in (0 : ℝ)..s, v u

def regularizedTimeClock (v : ℝ → ℝ) (a b ε s : ℝ) : ℝ :=
  a + (b - a) / (speedPrimitive v 1 + ε) * speedPrimitive (fun u => v u + ε) s

def regularizedPathCost (v : ℝ → ℝ) (a b ε s : ℝ) : ℝ :=
  (speedPrimitive v 1 + ε) / (b - a) * speedPrimitive v s

theorem speedPrimitive_hasDerivAt {v : ℝ → ℝ} (hv : Continuous v) (s : ℝ) :
    HasDerivAt (speedPrimitive v) (v s) s :=
  intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable (μ := volume) 0 s)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

theorem regularizedTimeClock_hasDerivAt {v : ℝ → ℝ} (hv : Continuous v) (a b ε s : ℝ) :
    HasDerivAt (regularizedTimeClock v a b ε)
      ((b - a) / (speedPrimitive v 1 + ε) * (v s + ε)) s := by
  exact ((speedPrimitive_hasDerivAt (hv.add continuous_const) s).const_mul _).const_add a

theorem regularizedPathCost_hasDerivAt {v : ℝ → ℝ} (hv : Continuous v) (a b ε s : ℝ) :
    HasDerivAt (regularizedPathCost v a b ε)
      ((speedPrimitive v 1 + ε) / (b - a) * v s) s :=
  (speedPrimitive_hasDerivAt hv s).const_mul _

theorem regularizedTimeClock_zero (v : ℝ → ℝ) (a b ε : ℝ) :
    regularizedTimeClock v a b ε 0 = a := by simp [regularizedTimeClock, speedPrimitive]

theorem regularizedTimeClock_one {v : ℝ → ℝ} (hv : Continuous v) (a b ε : ℝ)
    (hq : speedPrimitive v 1 + ε ≠ 0) : regularizedTimeClock v a b ε 1 = b := by
  have hi : speedPrimitive (fun u => v u + ε) 1 = speedPrimitive v 1 + ε := by
    rw [speedPrimitive, intervalIntegral.integral_add (hv.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul, speedPrimitive]
  rw [regularizedTimeClock, hi, div_mul_cancel₀ _ hq]
  ring

theorem regularizedTimeClock_properties {v : ℝ → ℝ} (hv : Continuous v)
    (hnonneg : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ v s)
    (a b ε : ℝ) (hab : a < b) (hε : 0 < ε) :
    Set.MapsTo (regularizedTimeClock v a b ε) (Set.Icc (0 : ℝ) 1) (Set.Icc a b) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        0 < (b - a) / (speedPrimitive v 1 + ε) * (v s + ε) ∧
        v s ^ 2 / 2 ≤
          ((b - a) / (speedPrimitive v 1 + ε) * (v s + ε)) *
            ((speedPrimitive v 1 + ε) / (b - a) * v s) := by
  have hL : 0 ≤ speedPrimitive v 1 := intervalIntegral.integral_nonneg zero_le_one hnonneg
  have hq : 0 < speedPrimitive v 1 + ε := add_pos_of_nonneg_of_pos hL hε
  have hderpos (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      0 < (b - a) / (speedPrimitive v 1 + ε) * (v s + ε) :=
    mul_pos (div_pos (sub_pos.mpr hab) hq) (add_pos_of_nonneg_of_pos (hnonneg s hs) hε)
  have hm : MonotoneOn (regularizedTimeClock v a b ε) (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
      (fun s _ => (regularizedTimeClock_hasDerivAt hv a b ε s).continuousAt.continuousWithinAt)
    · intro s _
      exact (regularizedTimeClock_hasDerivAt hv a b ε s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(regularizedTimeClock_hasDerivAt hv a b ε s).deriv]
      exact (hderpos s (interior_subset hs)).le
  constructor
  · intro s hs
    have hlo := hm (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num) hs hs.1
    have hhi := hm hs (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num) hs.2
    rw [regularizedTimeClock_zero] at hlo
    rw [regularizedTimeClock_one hv a b ε hq.ne'] at hhi
    exact ⟨hlo, hhi⟩
  · intro s hs
    refine ⟨hderpos s hs, ?_⟩
    have heq : ((b - a) / (speedPrimitive v 1 + ε) * (v s + ε)) *
        ((speedPrimitive v 1 + ε) / (b - a) * v s) = v s * (v s + ε) := by
      field_simp [hq.ne', (sub_pos.mpr hab).ne']
      <;> ring
    rw [heq]
    nlinarith [mul_nonneg (hnonneg s hs) hε.le, sq_nonneg (v s)]

end Yau.NodeProofs.C01Aux
