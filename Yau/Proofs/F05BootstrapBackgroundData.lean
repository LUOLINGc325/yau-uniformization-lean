import Yau.Proofs.F05BootstrapBackgroundWords
import Yau.Proofs.F05BootstrapBackgroundHolder

/-! Actual smooth fixed backgrounds discharge every finite background
word datum used by the nonlinear coefficient construction. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic
variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_smooth_background_good_diff {ν : Option (RIdx n)} {T : ℝ}
    {f : Point n → V} (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (d : Option (RIdx n)) : F05GoodDiffOn T d f (F05PosPatch ν T) := by
  intro z hz
  have hx : z.1 ∈ Metric.ball (0 : Space n) 3 :=
    Metric.ball_subset_ball (by norm_num : (2 : ℝ) ≤ 3) hz.1.2
  cases d with
  | none =>
    have hSlice : ContDiffOn ℝ ∞ (fun t => f (z.1,t)) (Ioc 0 T) :=
      hf.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht => ⟨hx,ht⟩)
    exact hSlice.differentiableOn (by simp) z.2 hz.2
  | some k =>
    have hSlice : ContDiffOn ℝ ∞ (fun x => f (x,z.2)) (Metric.ball 0 3) :=
      hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx => ⟨hx,hz.2⟩)
    have hDiff := (hSlice.differentiableOn (by simp) z.1 hx).differentiableAt
      (Metric.isOpen_ball.mem_nhds hx)
    have hLine : HasDerivAt (fun a : ℝ => z.1+a • realVec k) (realVec k) 0 := by
      simpa only [id_eq,one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const (realVec k)).const_add z.1
    exact (hDiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hLine (by simp)).differentiableAt

theorem F05_smooth_background_word_data {ν : Option (RIdx n)} {T α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {f : Point n → V}
    (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (β : List (Option (RIdx n))) :
    F05LocalHolder α ν T (F05GoodWord T β f) ∧
      ∀ d, F05GoodDiffOn T d (F05GoodWord T β f) (F05PosPatch ν T) := by
  have hSmooth := F05_smooth_background_good_words Metric.isOpen_ball hf β
  exact ⟨F05_positive_smooth_local_holder hα hα1 hSmooth,
    fun d => F05_smooth_background_good_diff hSmooth d⟩

end Yau.Proofs.F05Aux
