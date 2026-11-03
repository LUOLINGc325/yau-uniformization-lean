import Yau.Proofs.F05BootstrapNormalHessianContDiff
import Yau.Proofs.F05BootstrapJointOrderStep
import Yau.Proofs.F05BootstrapNonlinearGoodWords

/-! The actual outer finite-order induction closes all joint derivatives
of the value/normal-first family. The inner Hessian recursion is proved,
so no normal higher derivative or smooth exponential is a premise. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ}

theorem F05_zero_trace_physical_good_family_smooth {T α lam upper r s : ℝ} (j : RIdx n)
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    (hr : 0 < r) (hr2 : r < 2) (hs : 0 < s) (hsT : s < T)
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (H J u : Point n → ℝ)
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun z => B z i) (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hH : ContDiffOn ℝ ∞ H (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hJ : ContDiffOn ℝ ∞ J (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hu : F05LocalSchauder α (some j) T u) (hFace : F05ZeroFace (some j) T u)
    (hEll : Elliptic (F05PosPatch (some j) T) (fun z => Real.exp (-u z) • A z) lam upper)
    (hPDE : ∀ z ∈ F05PosPatch (some j) T,
      F05RelOp (F05PosSpace (some j)) (Ioc 0 T) (fun z => Real.exp (-u z) • A z)
        (fun z i => Real.exp (-u z)*B z i) u z = Real.exp (-u z)*H z+J z) :
    (∀ β : List (Option (RIdx n)), F05GoodList (some j) β →
      ContDiffOn ℝ ∞ (F05GoodWord T β u) (region (some j) r ×ˢ Icc s T)) ∧
    (∀ β : List (Option (RIdx n)), F05GoodList (some j) β →
      ContDiffOn ℝ ∞ (F05NormalWord T j β u) (region (some j) r ×ˢ Icc s T)) := by
  let Q := region (some j) r ×ˢ Icc s T
  have hQ : Q ⊆ F05PosPatch (some j) T := F05_receiving_subset_posPatch (some j) hr2 hs
  have hAll := F05_zero_trace_nonlinear_good_words hT hα hα1 A B H J u hA hB hH hJ hu hFace hEll hPDE
  have hWords := fun β hβ => (hAll β hβ).1
  have hEquations := fun β hβ => (hAll β hβ).2
  have hFinite (k : ℕ) :
      (∀ β : List (Option (RIdx n)), F05GoodList (some j) β → ContDiffOn ℝ k (F05GoodWord T β u) Q) ∧
      (∀ β : List (Option (RIdx n)), F05GoodList (some j) β → ContDiffOn ℝ k (F05NormalWord T j β u) Q) := by
    induction k with
    | zero =>
      constructor
      · intro β hβ
        exact contDiffOn_zero.mpr ((F05_local_schauder_to_relative (hWords β hβ)).1.mono hQ)
      · intro β hβ
        apply contDiffOn_zero.mpr
        have hC := (F05_local_schauder_to_relative (hWords β hβ)).2.1.mono hQ
        exact (ContinuousLinearMap.apply ℝ ℝ (realVec j)).continuous.comp_continuousOn hC
    | succ k ih =>
      have hHessian := F05_word_hessian_contDiff j hQ A B H J u hA hB hH hJ hEll hWords hEquations ih.1 ih.2
      exact F05_joint_family_successor j hr hr2 hs hsT u hWords ih.1 ih.2 hHessian
  constructor
  · intro β hβ
    exact contDiffOn_infty.mpr (fun k => (hFinite k).1 β hβ)
  · intro β hβ
    exact contDiffOn_infty.mpr (fun k => (hFinite k).2 β hβ)

end Yau.Proofs.F05Aux
