import Yau.Proofs.C06EnergySupport
import Yau.Proofs.C06LogCalculus

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C06Aux

open Yau Yau.Blueprint Yau.LeafProofs L12Aux

variable {n : ℕ}

/-- A smooth upper support for the logarithmic distance-square, also at cut points. -/
theorem logDistanceSquare_strictUpperSupport (X : KahlerManifold n)
    (o q : Pt X) (hne : o ≠ q) :
    ∃ S : ComplexVector n → ℝ,
      ContDiffAt ℝ 2 S (chartPt q q) ∧
      S (chartPt q q) = Real.log (inducedDistance X.metric.form o q ^ 2) ∧
      (∀ᶠ z in 𝓝 (chartPt q q),
        Real.log (inducedDistance X.metric.form o (chartInv q z) ^ 2) ≤ S z) ∧
      ∃ v : ComplexVector n, leviDirection (leviC S (chartPt q q)) v < 0 := by
  obtain ⟨E, v, hE, hval, hmajor, hv, hLevi, hFirst⟩ :=
    distanceSquare_strictUpperSupport X o q hne
  have hi : chartInv q (chartPt q q) = q :=
    (extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q)
  have hEq : inChart q E (chartPt q q) = E q := by
    change E (chartInv q (chartPt q q)) = E q
    rw [hi]
  have hd : 0 < inducedDistance X.metric.form o q :=
    lt_of_le_of_ne (X.metric.induced_distance_nonneg _ _)
      (Ne.symm (fun h => hne (X.metric.induced_distance_eq_zero.mp h)))
  have hp : 0 < inChart q E (chartPt q q) := by
    rw [hEq, hval]
    exact sq_pos_of_pos hd
  refine ⟨Real.log ∘ inChart q E, (Real.contDiffAt_log.mpr hp.ne').comp _ hE, ?_, ?_, v, ?_⟩
  · simp only [Function.comp_apply, hEq, hval]
  · have hInv : Tendsto (chartInv q) (𝓝 (chartPt q q)) (𝓝 q) := by
      have H := (continuousAt_extChartAt_symm (I := ComplexModel n) q).tendsto
      change Tendsto (chartInv q) (𝓝 (chartPt q q)) (𝓝 (chartInv q (chartPt q q))) at H
      rwa [hi] at H
    have hpos : ∀ᶠ y in 𝓝 q, 0 < inducedDistance X.metric.form o y :=
      ((continuous_distFrom X.metric o).continuousAt).eventually (lt_mem_nhds hd)
    filter_upwards [hInv.eventually hmajor, hInv.eventually hpos] with z hz hpz
    exact Real.log_le_log (sq_pos_of_pos hpz) hz
  · apply log_levi_neg hE hp
    · rwa [hEq, hval]
    · rwa [hEq, hval]

end Yau.Proofs.C06Aux
