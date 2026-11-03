import Yau.Proofs.F01ClosedLeviLimit
import Yau.Proofs.F01ClosedTimeDerivative

/-! Actual jet limits tolerate the finitely many approximants which have
not yet reached a chart or a closed horizon. Both initial and final time
faces are retained in the time and Levi limits. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ}

theorem eventual_closed_levi_limit_of_jets
    {S : Set (ComplexVector n)} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (f : ℕ → ComplexVector n × ℝ → ℝ) (g : ComplexVector n × ℝ → ℝ)
    (hf : ∀ᶠ m in atTop, ContDiffOn ℝ ∞ (f m) (S ×ˢ I))
    (hg : ContDiffOn ℝ ∞ g (S ×ˢ I))
    (hconv : TendstoUniformlyOn
      (fun m p => iteratedFDerivWithin ℝ 2 (f m) (S ×ˢ I) p)
      (iteratedFDerivWithin ℝ 2 g (S ×ˢ I)) atTop (S ×ˢ I))
    {x : ComplexVector n} (hx : x ∈ S) {t : ℝ} (ht : t ∈ I) :
    Tendsto (fun m => leviC (fun z => f m (z,t)) x) atTop
      (𝓝 (leviC (fun z => g (z,t)) x)) := by
  classical
  let fs : ℕ → ComplexVector n × ℝ → ℝ :=
    fun m => if ContDiffOn ℝ ∞ (f m) (S ×ˢ I) then f m else g
  have hfs (m : ℕ) : ContDiffOn ℝ ∞ (fs m) (S ×ˢ I) := by
    dsimp only [fs]
    split_ifs with hm
    · exact hm
    · exact hg
  have heq : ∀ᶠ m in atTop, fs m = f m :=
    hf.mono (fun m hm => by simp only [fs, if_pos hm])
  have hconv' : TendstoUniformlyOn
      (fun m p => iteratedFDerivWithin ℝ 2 (fs m) (S ×ˢ I) p)
      (iteratedFDerivWithin ℝ 2 g (S ×ˢ I)) atTop (S ×ˢ I) :=
    hconv.congr (heq.mono (fun m hm => fun p _ => by rw [hm]))
  have hLevi : Tendsto (fun m => leviC (fun z => fs m (z,t)) x) atTop
      (𝓝 (leviC (fun z => g (z,t)) x)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact closed_levi_entry_limit_of_jets hS hI fs g hfs hg hconv' hx ht i j
  exact hLevi.congr' (heq.mono (fun m hm => by rw [hm]))

theorem eventual_closed_time_derivative_limit_of_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} {I : Set ℝ} (hS : IsOpen S) (hI : UniqueDiffOn ℝ I)
    (f : ℕ → E × ℝ → F) (g : E × ℝ → F)
    (hf : ∀ᶠ m in atTop, ContDiffOn ℝ ∞ (f m) (S ×ˢ I))
    (hg : ContDiffOn ℝ ∞ g (S ×ˢ I))
    (hconv : TendstoUniformlyOn
      (fun m p => iteratedFDerivWithin ℝ 1 (f m) (S ×ˢ I) p)
      (iteratedFDerivWithin ℝ 1 g (S ×ˢ I)) atTop (S ×ˢ I))
    {x : E} (hx : x ∈ S) {t : ℝ} (ht : t ∈ I) :
    Tendsto (fun m => derivWithin (fun s => f m (x,s)) I t) atTop
      (𝓝 (derivWithin (fun s => g (x,s)) I t)) := by
  have hUnique : UniqueDiffWithinAt ℝ (S ×ˢ I) (x,t) :=
    (hS.uniqueDiffOn.prod hI) (x,t) ⟨hx,ht⟩
  have hEval : Continuous
      (fun D : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E × ℝ) F => D ![(0,1)]) := by
    fun_prop
  have hLimit := hEval.continuousAt.tendsto.comp
    (hconv.tendsto_at (show (x,t) ∈ S ×ˢ I from ⟨hx,ht⟩))
  have hValue (q : E × ℝ → F) (hq : ContDiffOn ℝ ∞ q (S ×ˢ I)) :
      iteratedFDerivWithin ℝ 1 q (S ×ˢ I) (x,t) ![(0,1)] =
        derivWithin (fun s => q (x,s)) I t := by
    rw [iteratedFDerivWithin_one_apply hUnique]
    exact (time_derivWithin_eq_joint_within hI (hq.differentiableOn (by simp)) hx ht).symm
  rw [hValue g hg] at hLimit
  exact hLimit.congr' (hf.mono (fun m hm => hValue (f m) hm))

end Yau.NodeProofs.F01Aux
