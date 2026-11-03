import Yau.Proofs.F05AtlasCompactness
import Yau.Proofs.F05PhysicalManifoldOperator

/-! The native computed maximum argument applies to the same compact
manifold domain, with no artificial chart-rim boundary data. -/

open Set
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_intrinsic_sub_timeAffine {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {T : ℝ} (hT : 0 < T) (w : M.Carrier → ℝ → ℝ)
    (hC2 : ∀ i, C2 (F05Q A i T) (pull A i w)) (δ : ℝ)
    {x : M.Carrier} (hx : x ∈ closure O) {t : ℝ} (ht : t ∈ Icc 0 T) :
    F05IntrinsicLinearOperator c h T (fun x t => w x t-δ*(t+1)) x t =
      F05IntrinsicLinearOperator c h T w x t-δ := by
  obtain ⟨i,z,hz,heq⟩ := F05_cover hA hx
  rw [← heq]
  have hp : (z,t) ∈ F05Q A i T := ⟨hz,ht⟩
  have hNew : C2 (F05Q A i T) (pull A i (fun x t => w x t-δ*(t+1))) :=
    c2_sub_timeAffine hT (hC2 i) δ
  have hNewEq := F05_intrinsic_operator_eq_chart hA h c T
    (fun x t => w x t-δ*(t+1)) i (p := (z,t)) hz (hNew.2.2.2.2.1 (z,t) hp)
  have hOldEq := F05_intrinsic_operator_eq_chart hA h c T w i (p := (z,t)) hz
    ((hC2 i).2.2.2.2.1 (z,t) hp)
  rw [hNewEq,hOldEq]
  exact linearOp_sub_timeAffine hT (hC2 i) δ hp

theorem F05_strict_manifold_maximum {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {T lam upper : ℝ} (w : M.Carrier → ℝ → ℝ)
    (hCont : ContinuousOn (fun p : M.Carrier × ℝ => w p.1 p.2) (closure O ×ˢ Icc 0 T))
    (hC2 : ∀ i, C2 (F05Q A i T) (pull A i w))
    (hEll : ∀ i, Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper)
    (hInit : ∀ x ∈ closure O, w x 0 ≤ 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t ≤ 0)
    (hOp : ∀ x ∈ O, ∀ t ∈ Ioc 0 T, F05IntrinsicLinearOperator c h T w x t < 0) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, w x t ≤ 0 := by
  intro x hx t ht
  by_contra hn
  have hPos : 0 < w x t := lt_of_not_ge hn
  obtain ⟨q,hq,hMax⟩ := ((F05_atlas_closure_compact hA).prod isCompact_Icc).exists_isMaxOn
    ⟨(x,t),hx,ht⟩ hCont
  have hqPos : 0 < w q.1 q.2 := hPos.trans_le (hMax (show (x,t) ∈ closure O ×ˢ Icc 0 T from ⟨hx,ht⟩))
  have hOpen := F05_atlas_domain_isOpen hA
  have hqO : q.1 ∈ O := by
    by_contra hOut
    have hFrontier : q.1 ∈ frontier O := ⟨hq.1,by simpa only [hOpen.interior_eq] using hOut⟩
    exact not_lt_of_ge (hBoundary q.1 hFrontier q.2 hq.2) hqPos
  have hqt : 0 < q.2 := by
    by_contra hNot
    have hZero : q.2 = 0 := le_antisymm (le_of_not_gt hNot) hq.2.1
    have hh : w q.1 q.2 ≤ 0 := by simpa only [hZero] using hInit q.1 hq.1
    exact not_lt_of_ge hh hqPos
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hA.2.1 hq.1)
  obtain ⟨z,hz,heq⟩ := hi
  have hzD : z ∈ F05D A i := region_mono (A.normal i) (by norm_num : (1 : ℝ) ≤ 2) hz
  obtain ⟨_,_,_,_,_,_,_,hPhysical⟩ := hA.1 i
  have hzModel : z ∈ F05ModelOpen A i := (F05ModelOpen_mem_iff A i z).mpr
    ((hPhysical z (F05D_mem_ball hzD)).1.mp (by rwa [heq]))
  have hzInterior : z ∈ interior (F05D A i) := F05D_interior_of_model A i hzModel (hz.1.trans_lt (by norm_num))
  have hRegular : closure (interior (F05D A i)) = F05D A i := by
    rw [(F05D_convex A i).closure_interior_eq_closure_of_nonempty_interior (F05D_interior_nonempty A i),
      (F05D_isClosed A i).closure_eq]
  have hMaxChart : IsMaxOn (pull A i w) (cylinder (closure (interior (F05D A i))) 0 T) (z,q.2) := by
    rw [hRegular]
    intro p hp
    have hh := hMax (show (lift A i p.1,p.2) ∈ closure O ×ˢ Icc 0 T from
      ⟨F05D_lift_mem_closure hA hp.1,hp.2⟩)
    change w (lift A i p.1) p.2 ≤ w (lift A i z) q.2
    rwa [heq]
  have hNonneg := linearOp_nonneg_at_max (b := F05FlowDrift A i h c) isOpen_interior
    (show C2 (cylinder (closure (interior (F05D A i))) 0 T) (pull A i w) by rw [hRegular]; exact hC2 i)
    (show Elliptic (cylinder (closure (interior (F05D A i))) 0 T) (F05FlowPrincipal A i h c) lam upper by
      rw [hRegular]; exact hEll i)
    (show (z,q.2) ∈ interior (F05D A i) ×ˢ Ioc 0 T from ⟨hzInterior,hqt,hq.2.2⟩) hMaxChart
  rw [hRegular] at hNonneg
  have hIdentity := F05_intrinsic_operator_eq_chart hA h c T w i (p := (z,q.2)) hzD
    ((hC2 i).2.2.2.2.1 (z,q.2) ⟨hzD,hq.2⟩)
  rw [heq] at hIdentity
  have hGe : 0 ≤ F05IntrinsicLinearOperator c h T w q.1 q.2 := hNonneg.trans_eq hIdentity.symm
  exact not_lt_of_ge hGe (hOp q.1 hqO q.2 ⟨hqt,hq.2.2⟩)

theorem F05_manifold_maximum {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (c : M.Carrier → ℝ → ℝ)
    {T lam upper : ℝ} (hT : 0 < T) (w : M.Carrier → ℝ → ℝ)
    (hCont : ContinuousOn (fun p : M.Carrier × ℝ => w p.1 p.2) (closure O ×ˢ Icc 0 T))
    (hC2 : ∀ i, C2 (F05Q A i T) (pull A i w))
    (hEll : ∀ i, Elliptic (F05Q A i T) (F05FlowPrincipal A i h c) lam upper)
    (hInit : ∀ x ∈ closure O, w x 0 ≤ 0)
    (hBoundary : ∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t ≤ 0)
    (hOp : ∀ x ∈ O, ∀ t ∈ Ioc 0 T, F05IntrinsicLinearOperator c h T w x t ≤ 0) :
    ∀ x ∈ closure O, ∀ t ∈ Icc 0 T, w x t ≤ 0 := by
  intro x hx t ht
  by_contra hn
  have hPos : 0 < w x t := lt_of_not_ge hn
  let δ := w x t/(2*(t+1))
  have hDen : 0 < 2*(t+1) := by linarith [ht.1]
  have hδ : 0 < δ := div_pos hPos hDen
  let v := fun x t => w x t-δ*(t+1)
  have hContV : ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (closure O ×ˢ Icc 0 T) :=
    hCont.sub (by fun_prop)
  have hC2V (i : Fin A.count) : C2 (F05Q A i T) (pull A i v) := c2_sub_timeAffine hT (hC2 i) δ
  have hInitV (y : M.Carrier) (hy : y ∈ closure O) : v y 0 ≤ 0 := by
    dsimp only [v]
    nlinarith [hInit y hy]
  have hBoundaryV (y : M.Carrier) (hy : y ∈ frontier O) (s : ℝ) (hs : s ∈ Icc 0 T) : v y s ≤ 0 := by
    dsimp only [v]
    nlinarith [hBoundary y hy s hs,mul_nonneg hδ.le hs.1]
  have hOpV (y : M.Carrier) (hy : y ∈ O) (s : ℝ) (hs : s ∈ Ioc 0 T) :
      F05IntrinsicLinearOperator c h T v y s < 0 := by
    dsimp only [v]
    rw [F05_intrinsic_sub_timeAffine hA h c hT w hC2 δ (subset_closure hy) ⟨hs.1.le,hs.2⟩]
    linarith [hOp y hy s hs]
  have hNonpos := F05_strict_manifold_maximum hA h c v hContV hC2V hEll hInitV hBoundaryV hOpV x hx t ht
  have hCancel : δ*(t+1) = w x t/2 := by
    have htOne : t+1 ≠ 0 := ne_of_gt (by linarith [ht.1])
    dsimp only [δ]
    field_simp [htOne]
    <;> ring
  change w x t-δ*(t+1) ≤ 0 at hNonpos
  rw [hCancel] at hNonpos
  linarith

end Yau.Proofs.F05Aux
