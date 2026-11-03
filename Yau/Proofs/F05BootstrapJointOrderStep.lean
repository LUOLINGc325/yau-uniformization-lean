import Yau.Proofs.F05BootstrapJointFirst
import Yau.Proofs.F05BootstrapJointMaps
import Yau.Proofs.F05BootstrapNormalGradientContDiff

/-! With the current Hessians recovered, the actual joint derivative
maps raise the value/normal-first-derivative family by one finite order. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ}

theorem F05_joint_family_successor {T α r s : ℝ} {k : ℕ} (j : RIdx n)
    (hr : 0 < r) (hr2 : r < 2) (hs : 0 < s) (hsT : s < T) (u : Point n → ℝ)
    (hWords : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      F05LocalSchauder α (some j) T (F05GoodWord T γ u))
    (hJoint : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      ContDiffOn ℝ k (F05GoodWord T γ u) (region (some j) r ×ˢ Icc s T))
    (hNormal : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      ContDiffOn ℝ k (F05NormalWord T j γ u) (region (some j) r ×ˢ Icc s T))
    (hHessian : ∀ γ : List (Option (RIdx n)), F05GoodList (some j) γ →
      ContDiffOn ℝ k (F05RelDD (F05PosSpace (some j)) (F05GoodWord T γ u))
        (region (some j) r ×ˢ Icc s T)) :
    (∀ β : List (Option (RIdx n)), F05GoodList (some j) β →
      ContDiffOn ℝ (k+1) (F05GoodWord T β u) (region (some j) r ×ˢ Icc s T)) ∧
    (∀ β : List (Option (RIdx n)), F05GoodList (some j) β →
      ContDiffOn ℝ (k+1) (F05NormalWord T j β u) (region (some j) r ×ˢ Icc s T)) := by
  let X := F05PosSpace (some j)
  let Q := region (some j) r ×ˢ Icc s T
  have hUnique : UniqueDiffOn ℝ Q := (F05_region_uniqueDiffOn (some j) hr).prod (uniqueDiffOn_Icc hsT)
  have hQ : Q ⊆ F05PosPatch (some j) T := F05_receiving_subset_posPatch (some j) hr2 hs
  have hTimeGood (β : List (Option (RIdx n))) (hβ : F05GoodList (some j) β) :
      F05GoodList (some j) (none::β) := (F05GoodList_cons (some j) none β).mpr ⟨by trivial,hβ⟩
  constructor
  · intro β hβ
    have hGradient := F05_word_gradient_contDiff j hQ u hWords hJoint hNormal β hβ
    have hTime : ContDiffOn ℝ k (F05RelT (Ioc 0 T) (F05GoodWord T β u)) Q :=
      hJoint (none::β) (hTimeGood β hβ)
    have hD := F05_product_derivative_contDiff hGradient hTime
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := k) hUnique).mpr
    refine ⟨by simp,fun z => F05ProductDerivative
      (F05RelD X (F05GoodWord T β u) z) (F05RelT (Ioc 0 T) (F05GoodWord T β u) z),hD,?_⟩
    intro z hz
    exact F05_relative_joint_derivative hr hr2 hs hsT (F05_local_schauder_to_relative (hWords β hβ)) hz
  · intro β hβ
    let L : (Space n →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (realVec j)
    have hAC : ContDiffOn ℝ k (fun z => L.comp (F05RelDD X (F05GoodWord T β u) z)) Q :=
      contDiffOn_const.clm_comp (hHessian β hβ)
    have hJC : ContDiffOn ℝ k (F05NormalWord T j (none::β) u) Q :=
      hNormal (none::β) (hTimeGood β hβ)
    have hD := F05_product_derivative_contDiff hAC hJC
    apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (n := k) hUnique).mpr
    refine ⟨by simp,fun z => F05ProductDerivative
      (L.comp (F05RelDD X (F05GoodWord T β u) z)) (F05NormalWord T j (none::β) u z),hD,?_⟩
    intro z hz
    exact F05_gradient_component_joint_derivative hr hr2 hs hsT
      (hWords β hβ) (hWords (none::β) (hTimeGood β hβ)) j hz

end Yau.Proofs.F05Aux
