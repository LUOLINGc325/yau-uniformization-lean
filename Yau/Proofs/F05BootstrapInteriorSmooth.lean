import Yau.Proofs.F05BootstrapJointOrderStep

/-! Interior charts have no excluded spatial letter. Actual good-word
Schauder regularity therefore closes the finite joint-order induction
directly, including the one-sided terminal time and dimension zero. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ}

theorem F05_interior_good_family_smooth {T α r s : ℝ}
    (hr : 0 < r) (hr2 : r < 2) (hs : 0 < s) (hsT : s < T) (u : Point n → ℝ)
    (hWords : ∀ γ : List (Option (RIdx n)), F05GoodList none γ →
      F05LocalSchauder α none T (F05GoodWord T γ u)) :
    ∀ β : List (Option (RIdx n)), F05GoodList none β →
      ContDiffOn ℝ ∞ (F05GoodWord T β u) (region none r ×ˢ Icc s T) := by
  let Q := region (none : Option (RIdx n)) r ×ˢ Icc s T
  let X := F05PosSpace (none : Option (RIdx n))
  have hQ : Q ⊆ F05PosPatch none T := F05_receiving_subset_posPatch none hr2 hs
  have hUnique : UniqueDiffOn ℝ Q := (F05_region_uniqueDiffOn none hr).prod (uniqueDiffOn_Icc hsT)
  have hFinite (k : ℕ) : ∀ β : List (Option (RIdx n)), F05GoodList none β →
      ContDiffOn ℝ k (F05GoodWord T β u) Q := by
    induction k with
    | zero =>
      intro β hβ
      exact contDiffOn_zero.mpr ((F05_local_schauder_to_relative (hWords β hβ)).1.mono hQ)
    | succ k ih =>
      intro β hβ
      have hGradient : ContDiffOn ℝ k (F05RelD X (F05GoodWord T β u)) Q := by
        apply F05_covector_contDiff_of_components
        intro i
        have hGood : F05GoodLetter (none : Option (RIdx n)) (some i) := by trivial
        have hIβ : F05GoodList none (some i::β) := (F05GoodList_cons none (some i) β).mpr ⟨hGood,hβ⟩
        have hEq := F05_good_gradient_component_eq hGood (hWords β hβ)
        exact (ih (some i::β) hIβ).congr (fun z hz => hEq (hQ hz))
      have hTimeGood : F05GoodList (none : Option (RIdx n)) (none::β) :=
        (F05GoodList_cons none none β).mpr ⟨by trivial,hβ⟩
      have hTime : ContDiffOn ℝ k (F05RelT (Ioc 0 T) (F05GoodWord T β u)) Q := ih (none::β) hTimeGood
      have hD := F05_product_derivative_contDiff hGradient hTime
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := k) hUnique).mpr
      refine ⟨by simp,fun z => F05ProductDerivative
        (F05RelD X (F05GoodWord T β u) z) (F05RelT (Ioc 0 T) (F05GoodWord T β u) z),hD,?_⟩
      intro z hz
      exact F05_relative_joint_derivative hr hr2 hs hsT (F05_local_schauder_to_relative (hWords β hβ)) hz
  intro β hβ
  exact contDiffOn_infty.mpr (fun k => hFinite k β hβ)

end Yau.Proofs.F05Aux
