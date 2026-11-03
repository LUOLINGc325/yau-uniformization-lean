import Yau.Proofs.F05NormalProfile
import Yau.Proofs.F04SeeleySmooth

/-! The certified scalar Seeley operator produces a true open spatial
extension of a fixed positive-time boundary profile. Its input product is
constructed from the actual physical chart, rather than assumed. -/

open Set
open scoped Topology ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
open Yau.F04Proof.Seeley
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_positive_boundary_profile_local_extension {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (i : Fin A.count) (j : RIdx n) (hν : A.normal i = some j)
    (w : M.Carrier → ℝ → ℝ) {τ T t : ℝ} (ht : t ∈ Icc τ T)
    (hInner : ∀ k, ContDiffOn ℝ ∞ (pull A k w)
      (region (A.normal k) (3/2) ×ˢ Icc τ T))
    {x : Space n} (hx : x ∈ Metric.ball 0 3) (hFace : realCoord x j = 0) :
    ∃ (V : Set (Space n)) (F : Space n → ℝ), IsOpen V ∧ x ∈ V ∧
      ContDiffOn ℝ ∞ F V ∧ ∀ z ∈ V, realCoord z j ≤ 0 → F z = pull A i w (z,t) := by
  obtain ⟨R,hR,hProfile⟩ := F05_smooth_normal_profile_product hA i j hν w ht hInner hx hFace
  let c : F05Tangential j := F05TangentPoint j x hFace
  let O0 : Set (F05Tangential j) := Metric.ball c R
  let W : Set (F05Tangential j) := Metric.ball c (R/2)
  let χ : ContDiffBump (0 : ℝ) := ⟨R/8,R/4,by positivity,by linarith⟩
  let f : F05Tangential j × ℝ → ℝ := fun q => pull A i w (F05NormalMergeMap j q,t)
  have hWc : IsCompact (closure W) :=
    (isCompact_closedBall c (R/2)).of_isClosed_subset isClosed_closure Metric.closure_ball_subset_closedBall
  have hWO : closure W ⊆ O0 := Metric.closure_ball_subset_closedBall.trans
    (Metric.closedBall_subset_ball (by linarith))
  have hZero : ∀ a : ℝ, R/4 ≤ a → χ a = 0 := by
    intro a ha
    apply χ.zero_of_le_dist
    change R/4 ≤ dist a 0
    rw [Real.dist_eq,sub_zero]
    exact ha.trans (le_abs_self a)
  have hOne : ∀ a : ℝ, |a| ≤ (R/4)/2 → χ a = 1 := by
    intro a ha
    apply χ.one_of_mem_closedBall
    change dist a 0 ≤ R/8
    rw [Real.dist_eq,sub_zero]
    linarith
  have hExt := seeleyExtend_contDiffOn Metric.isOpen_ball Metric.isOpen_ball hWc hWO
    (by positivity : (0 : ℝ) < R/4) (by linarith : R/4 < R) χ.contDiff hZero hOne hProfile
  let V : Set (Space n) := (F05NormalProduct j) ⁻¹' (W ×ˢ Iio R)
  let F : Space n → ℝ := fun z => seeleyExtend χ f (F05NormalProduct j z)
  have hV : IsOpen V := (Metric.isOpen_ball.prod isOpen_Iio).preimage (F05NormalProduct j).continuous
  have hxV : x ∈ V := by
    change F05NormalProduct j x ∈ W ×ˢ Iio R
    rw [F05_normal_product_face j hFace]
    exact ⟨Metric.mem_ball_self (by positivity),hR⟩
  refine ⟨V,F,hV,hxV,hExt.comp (F05NormalProduct j).contDiff.contDiffOn (fun z hz => hz),?_⟩
  intro z hz hzFace
  have hz0 : 0 ≤ (F05NormalProduct j z).2 := by
    change 0 ≤ -realCoordLinear j z
    simpa only [realCoordLinear_apply] using neg_nonneg.mpr hzFace
  change seeleyExtend χ f (F05NormalProduct j z) = _
  rw [seeleyExtend_eq_nonneg χ f _ hz0]
  change pull A i w (F05NormalMergeMap j (F05NormalSplitMap j z),t) = _
  rw [F05_normal_merge_split]

end Yau.Proofs.F05Aux
