import Yau.LeafProofs.L19HeatFamilyReal
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Uniform dyadic implicit Euler approximation of the actual heat multiplier. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace Yau.LeafProofs.L19Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Rational multiplier of one implicit Euler step. -/
def scalarEulerMultiplier (h s : ℝ) : ℝ := s / (h + (1 - h) * s)

theorem scalarEuler_denominator_pos {h s : ℝ} (hh : 0 < h)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : 0 < h + (1 - h) * s := by
  rcases lt_or_eq_of_le hs.2 with hs1 | rfl
  · have := mul_pos hh (sub_pos.mpr hs1)
    nlinarith [hs.1]
  · simp

theorem scalarEulerMultiplier_continuousOn {h : ℝ} (hh : 0 < h) :
    ContinuousOn (scalarEulerMultiplier h) (Set.Icc (0 : ℝ) 1) := by
  exact continuousOn_id.div (continuous_const.add
    (continuous_const.mul continuous_id)).continuousOn
    (fun s hs => (scalarEuler_denominator_pos hh hs).ne')

/-- The number of steps is always positive, including index zero. -/
def scalarEulerCount (k : ℕ) : ℕ := 2 ^ k

theorem scalarEulerCount_pos (k : ℕ) : 0 < scalarEulerCount k := pow_pos (by decide) _

theorem scalarEulerCount_cast_pos (k : ℕ) : 0 < (scalarEulerCount k : ℝ) := by
  exact_mod_cast scalarEulerCount_pos k

theorem scalarEulerCount_tendsto : Tendsto scalarEulerCount atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : ℕ))

def scalarEulerPowerMultiplier (t : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  scalarEulerMultiplier (t / scalarEulerCount k) s ^ scalarEulerCount k

theorem scalarEulerPowerMultiplier_continuousOn {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ContinuousOn (scalarEulerPowerMultiplier t k) (Set.Icc (0 : ℝ) 1) :=
  (scalarEulerMultiplier_continuousOn (div_pos ht (scalarEulerCount_cast_pos k))).pow _

theorem scalarEulerMultiplier_eq_inv {t s : ℝ} (hs : 0 < s) (k : ℕ) :
    scalarEulerMultiplier (t / scalarEulerCount k) s =
      (1 + (t * (1 / s - 1)) / scalarEulerCount k)⁻¹ := by
  have hN := (scalarEulerCount_cast_pos k).ne'
  unfold scalarEulerMultiplier
  field_simp
  ring

theorem scalarEulerPowerMultiplier_tendsto {t : ℝ} (_ht : 0 < t)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun k => scalarEulerPowerMultiplier t k s) atTop
      (𝓝 (scalarHeatMultiplier t s)) := by
  rcases hs.1.eq_or_lt with rfl | hs0
  · have hzero : ∀ k, scalarEulerPowerMultiplier t k 0 = 0 := by
      intro k
      simp [scalarEulerPowerMultiplier, scalarEulerMultiplier,
        Nat.ne_of_gt (scalarEulerCount_pos k)]
    simpa only [hzero, scalarHeatMultiplier, lt_self_iff_false, ite_false] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · have h := ((Real.tendsto_one_add_div_pow_exp (t * (1 / s - 1))).comp
      scalarEulerCount_tendsto).inv₀ (Real.exp_ne_zero _)
    convert h using 1
    · ext k
      simp only [scalarEulerPowerMultiplier, scalarEulerMultiplier_eq_inv hs0, inv_pow, Function.comp_apply]
    · simp only [scalarHeatMultiplier, hs0, ite_true, ← Real.exp_neg, one_div, neg_mul]

theorem scalarEulerPowerMultiplier_antitone {t : ℝ} (ht : 0 < t)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (fun k => scalarEulerPowerMultiplier t k s) := by
  apply antitone_nat_of_succ_le
  intro k
  rcases hs.1.eq_or_lt with rfl | hs0
  · simp [scalarEulerPowerMultiplier, scalarEulerMultiplier,
      Nat.ne_of_gt (scalarEulerCount_pos _)]
  · let a := t * (1 / s - 1)
    have ha : 0 ≤ a := mul_nonneg ht.le (by
      have := (one_le_div hs0).2 hs.2
      linarith)
    have hN := scalarEulerCount_cast_pos k
    have hN' : (scalarEulerCount (k + 1) : ℝ) = 2 * scalarEulerCount k := by
      simp [scalarEulerCount, pow_succ, mul_comm]
    have hNi : scalarEulerCount (k + 1) = 2 * scalarEulerCount k := by
      simp [scalarEulerCount, pow_succ, mul_comm]
    have hbase : 1 + a / (scalarEulerCount k : ℝ) ≤
        (1 + a / (scalarEulerCount (k + 1) : ℝ)) ^ 2 := by
      rw [hN']
      have heq : a / (↑(scalarEulerCount k) * 2) * 2 = a / scalarEulerCount k := by field_simp
      rw [mul_comm (2 : ℝ) (scalarEulerCount k)]
      nlinarith [sq_nonneg (a / (↑(scalarEulerCount k) * 2))]
    have hp : (1 + a / (scalarEulerCount k : ℝ)) ^ scalarEulerCount k ≤
        (1 + a / (scalarEulerCount (k + 1) : ℝ)) ^ scalarEulerCount (k + 1) := by
      have hp := pow_le_pow_left₀ (by positivity) hbase (scalarEulerCount k)
      simpa only [← pow_mul, ← hNi] using hp
    simp only [scalarEulerPowerMultiplier, scalarEulerMultiplier_eq_inv hs0, inv_pow]
    exact inv_anti₀ (by positivity) hp

/-- Dini's theorem upgrades the scalar dyadic limit to convergence in the
continuous-function norm on the entire interval, including spectral zero. -/
theorem scalarEulerPowerMultiplier_uniform {t : ℝ} (ht : 0 < t) :
    Tendsto (fun k => (⟨fun s : Set.Icc (0 : ℝ) 1 => scalarEulerPowerMultiplier t k s,
      (scalarEulerPowerMultiplier_continuousOn ht k).domRestrict⟩ :
        C(Set.Icc (0 : ℝ) 1, ℝ))) atTop
      (𝓝 (⟨fun s : Set.Icc (0 : ℝ) 1 => scalarHeatMultiplier t s,
        (scalarHeatMultiplier_continuous ht).comp continuous_subtype_val⟩ :
          C(Set.Icc (0 : ℝ) 1, ℝ))) := by
  apply ContinuousMap.tendsto_of_antitone_of_pointwise
  · intro k l hkl s
    exact scalarEulerPowerMultiplier_antitone ht s.property hkl
  · intro s
    exact scalarEulerPowerMultiplier_tendsto ht s.property

end Yau.LeafProofs.L19Aux
