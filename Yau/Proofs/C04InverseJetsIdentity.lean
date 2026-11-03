import Yau.Proofs.C04InverseJetsLeading

/-! The same local inverse gives the exact identity Taylor composition at every order. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Yau.Proofs.C04Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverseJet_norm_identity {m : ℕ} (hm : 0 < m) (w : E) :
    ‖iteratedFDeriv ℝ m (id : E → E) w‖ ≤ 1 := by
  have hfid : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E := by
    funext x
    exact fderiv_id
  cases m with
  | zero => omega
  | succ k =>
    cases k with
    | zero =>
      rw [norm_iteratedFDeriv_one, hfid]
      exact ContinuousLinearMap.norm_id_le
    | succ j =>
      rw [← norm_iteratedFDeriv_fderiv (n := j + 1), hfid]
      simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
      norm_num

theorem inverseJet_identity_bound (F ψ : E → E) {s : Set E} (hs : IsOpen s)
    (hF : ContDiff ℝ ∞ F) (hψ : ContDiffOn ℝ ∞ ψ s)
    (hcomp : ∀ w ∈ s, F (ψ w) = w) {w : E} (hw : w ∈ s)
    {m : ℕ} (hm : 0 < m) :
    ‖(ftaylorSeries ℝ F (ψ w)).taylorComp (ftaylorSeries ℝ ψ w) m‖ ≤ 1 := by
  have hψat : ContDiffAt ℝ ∞ ψ w := (hψ w hw).contDiffAt (hs.mem_nhds hw)
  rw [← iteratedFDeriv_comp hF.contDiffAt hψat (by simp : (m : ℕ∞ω) ≤ ∞)]
  have heq : F ∘ ψ =ᶠ[𝓝 w] (id : E → E) := by
    filter_upwards [hs.mem_nhds hw] with y hy
    exact hcomp y hy
  rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds]
  exact inverseJet_norm_identity hm w

end Yau.Proofs.C04Aux
