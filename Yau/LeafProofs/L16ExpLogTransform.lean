import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L16Log

/-- A globally smooth, strictly positive replacement for the identity. -/
def positiveIdentity (m x : ℝ) : ℝ :=
  m / 4 + (x - m / 4) * Real.smoothTransition ((x - m / 4) / (m / 4))

theorem positiveIdentity_pos {m : ℝ} (hm : 0 < m) (x : ℝ) :
    0 < positiveIdentity m x := by
  by_cases hx : x ≤ m / 4
  · have hz : (x - m / 4) / (m / 4) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (by positivity)
    simp [positiveIdentity, Real.smoothTransition.zero_of_nonpos hz, hm]
  · have hterm : 0 ≤ (x - m / 4) *
        Real.smoothTransition ((x - m / 4) / (m / 4)) :=
      mul_nonneg (by linarith) (Real.smoothTransition.nonneg _)
    unfold positiveIdentity
    linarith

theorem positiveIdentity_eq {m x : ℝ} (hm : 0 < m) (hx : m / 2 ≤ x) :
    positiveIdentity m x = x := by
  have ht : 1 ≤ (x - m / 4) / (m / 4) := by
    apply (le_div_iff₀ (by positivity : 0 < m / 4)).2
    linarith
  simp [positiveIdentity, Real.smoothTransition.one_of_one_le ht]

theorem positiveIdentity_contDiff (m : ℝ) : ContDiff ℝ ∞ (positiveIdentity m) := by
  unfold positiveIdentity
  fun_prop

/-- The transform is selected from m and B before any candidate solution.
It agrees with log on an open neighborhood of the whole interval [m,B]. -/
theorem exists_smooth_log_transform {m B : ℝ} (hm : 0 < m) (hmB : m ≤ B) :
    ∃ ℓ : ℝ → ℝ, ContDiff ℝ ∞ ℓ ∧ HasCompactSupport ℓ ∧
      EqOn ℓ Real.log (Ioo (m / 2) (B + 1)) ∧
      ∀ x ∈ Icc m B, ℓ =ᶠ[𝓝 x] Real.log := by
  have hB : 0 < B := lt_of_lt_of_le hm hmB
  let χ : ContDiffBump (0 : ℝ) :=
    { rIn := B + 1
      rOut := B + 2
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  let ℓ : ℝ → ℝ := fun x => χ x * Real.log (positiveIdentity m x)
  have hsmooth : ContDiff ℝ ∞ ℓ :=
    χ.contDiff.mul ((positiveIdentity_contDiff m).log
      (fun x => (positiveIdentity_pos hm x).ne'))
  have hcompact : HasCompactSupport ℓ := χ.hasCompactSupport.mul_right
  have heq : EqOn ℓ Real.log (Ioo (m / 2) (B + 1)) := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hxball : x ∈ Metric.closedBall (0 : ℝ) χ.rIn := by
      change dist x 0 ≤ B + 1
      simpa [Real.dist_eq, abs_of_pos hx0] using hx.2.le
    dsimp only [ℓ]
    rw [χ.one_of_mem_closedBall hxball, positiveIdentity_eq hm hx.1.le, one_mul]
  refine ⟨ℓ, hsmooth, hcompact, heq, ?_⟩
  intro x hx
  have hxopen : x ∈ Ioo (m / 2) (B + 1) := by
    constructor <;> linarith [hx.1, hx.2]
  filter_upwards [isOpen_Ioo.mem_nhds hxopen] with y hy
  exact heq hy

/-- Boundary agreement needs bounds only on q, and equality p=q on that boundary. -/
theorem smooth_log_transform_boundary_eq {α : Type*} {S : Set α}
    {m B : ℝ} (hm : 0 < m) {ℓ : ℝ → ℝ}
    (hℓ : EqOn ℓ Real.log (Ioo (m / 2) (B + 1)))
    {p q : α → ℝ} (hpq : EqOn p q S)
    (hq : ∀ x ∈ S, q x ∈ Icc m B) :
    EqOn (fun x => ℓ (p x)) (fun x => Real.log (q x)) S := by
  intro x hx
  change ℓ (p x) = Real.log (q x)
  rw [hpq hx]
  apply hℓ
  constructor <;> linarith [(hq x hx).1, (hq x hx).2]

end Yau.LeafProofs.L16Log
