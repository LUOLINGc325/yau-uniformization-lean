import Yau.Proofs.C06Annulus

noncomputable section
open Filter Set
open scoped Topology

namespace Yau.Proofs.C06Aux

open Yau Yau.Blueprint Yau.LeafProofs.L12Aux

variable {n : ℕ}

/-- Apply annular comparison at each center, with no assumed continuity of the psh function. -/
theorem real_psh_constant (X : KahlerManifold n) {v : Pt X → ℝ}
    (hv : IsPsh (fun x => (v x : EReal))) {B : ℝ} (hB : ∀ x, v x ≤ B) :
    ∀ x y, v x = v y := by
  have hle : ∀ o y : Pt X, v y ≤ v o := by
    intro o y
    letI := inducedMetricSpace X.metric
    have hδ : ∀ δ : ℝ, 0 < δ → v y ≤ v o + δ := by
      intro δ hδ
      have hnear : ∀ᶠ x in 𝓝 o, v x < v o + δ :=
        (upperSemicontinuous_of_coe hv.2.1) o (v o + δ) (by linarith)
      obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hnear
      let r : ℝ := R / 2
      have hr : 0 < r := half_pos hR
      have hlocal (x : Pt X) (hx : inducedDistance X.metric.form o x ≤ r) :
          v x ≤ v o + δ := by
        have hxBall : x ∈ Metric.ball o R := by
          rw [Metric.mem_ball, dist_comm]
          exact hx.trans_lt (half_lt_self hR)
        exact (hball hxBall).le
      by_cases hy : inducedDistance X.metric.form o y ≤ r
      · exact hlocal y hy
      · let L : ℝ := Real.log (inducedDistance X.metric.form o y ^ 2) - Real.log (r ^ 2)
        have hlim : Tendsto (fun ε : ℝ => (v o + δ) + ε * L) (𝓝[>] 0) (𝓝 (v o + δ)) := by
          have H : ContinuousAt (fun ε : ℝ => (v o + δ) + ε * L) 0 := by fun_prop
          simpa only [zero_mul, add_zero] using H.tendsto.mono_left nhdsWithin_le_nhds
        apply ge_of_tendsto hlim
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact logarithmic_barrier_comparison X hv hB o hr hε hlocal y (le_of_not_ge hy)
    exact le_of_forall_pos_le_add hδ
  intro x y
  exact le_antisymm (hle y x) (hle x y)

end Yau.Proofs.C06Aux
