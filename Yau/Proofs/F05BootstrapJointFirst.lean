import Yau.Proofs.F05BootstrapClosedProductDifferentiation
import Yau.Proofs.F05BootstrapTimeCommutation

/-! The actual solution and every first spatial gradient component have
genuine joint derivatives on closed physical caps. No joint derivative
of the Hessian is asserted before the normal recovery bootstrap. -/

open Set
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ}

theorem F05_relative_joint_derivative {ν : Option (RIdx n)} {r s T : ℝ}
    (hr : 0 < r) (hr2 : r < 2) (hs : 0 < s) (hsT : s < T)
    {u : Point n → ℝ} (hu : F05RelC2 (F05PosSpace ν) (Ioc 0 T) u)
    {z : Point n} (hz : z ∈ region ν r ×ˢ Icc s T) :
    HasFDerivWithinAt u (F05ProductDerivative (F05RelD (F05PosSpace ν) u z)
      (F05RelT (Ioc 0 T) u z)) (region ν r ×ˢ Icc s T) z := by
  have hSpace := F05_region_subset_posSpace ν hr2
  have hTime : Icc s T ⊆ Ioc 0 T := fun t ht => ⟨hs.trans_le ht.1,ht.2⟩
  have hSub : region ν r ×ˢ Icc s T ⊆ F05PosPatch ν T := fun p hp => ⟨hSpace hp.1,hTime hp.2⟩
  apply F05_closed_product_derivative (F05_region_convex ν r) (F05_region_closure_interior ν hr) hsT
    (F := u) (A := F05RelD (F05PosSpace ν) u) (J := F05RelT (Ioc 0 T) u)
    (hu.1.mono hSub) (hu.2.1.mono hSub) (hu.2.2.2.1.mono hSub)
  · intro t ht x hx
    exact (((hu.2.2.2.2.1 t (hTime ht) x (hSpace hx)).differentiableWithinAt
      (by norm_num)).hasFDerivWithinAt).mono hSpace
  · intro x hx t ht
    exact ((hu.2.2.2.2.2 (x,t) ⟨hSpace hx,hTime ht⟩).hasDerivWithinAt).mono hTime
  · exact hz

theorem F05_gradient_component_joint_derivative {ν : Option (RIdx n)} {r s T α : ℝ}
    (hr : 0 < r) (hr2 : r < 2) (hs : 0 < s) (hsT : s < T)
    {u : Point n → ℝ} (hu : F05LocalSchauder α ν T u)
    (htu : F05LocalSchauder α ν T (F05GoodPartial T none u)) (k : RIdx n)
    {z : Point n} (hz : z ∈ region ν r ×ˢ Icc s T) :
    HasFDerivWithinAt (fun p => F05RelD (F05PosSpace ν) u p (realVec k))
      (F05ProductDerivative
        ((ContinuousLinearMap.apply ℝ ℝ (realVec k)).comp (F05RelDD (F05PosSpace ν) u z))
        (F05RelD (F05PosSpace ν) (F05GoodPartial T none u) z (realVec k)))
      (region ν r ×ˢ Icc s T) z := by
  let Y := F05PosSpace ν
  let L : (Space n →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (realVec k)
  have hU := F05_local_schauder_to_relative hu
  have hW := F05_local_schauder_to_relative htu
  have hY := F05_posSpace_uniqueDiffOn ν
  have hSpace : region ν r ⊆ Y := F05_region_subset_posSpace ν hr2
  have hTime : Icc s T ⊆ Ioc 0 T := fun t ht => ⟨hs.trans_le ht.1,ht.2⟩
  have hSub : region ν r ×ˢ Icc s T ⊆ F05PosPatch ν T := fun p hp => ⟨hSpace hp.1,hTime hp.2⟩
  have hFC : ContinuousOn (fun p => L (F05RelD Y u p)) (region ν r ×ˢ Icc s T) :=
    L.continuous.comp_continuousOn (hU.2.1.mono hSub)
  have hAC : ContinuousOn (fun p => L.comp (F05RelDD Y u p)) (region ν r ×ˢ Icc s T) :=
    continuousOn_const.clm_comp (hU.2.2.1.mono hSub)
  have hJC : ContinuousOn (fun p => L (F05RelD Y (F05GoodPartial T none u) p))
      (region ν r ×ˢ Icc s T) := L.continuous.comp_continuousOn (hW.2.1.mono hSub)
  apply F05_closed_product_derivative (F05_region_convex ν r) (F05_region_closure_interior ν hr) hsT
    (F := fun p => L (F05RelD Y u p)) (A := fun p => L.comp (F05RelDD Y u p))
    (J := fun p => L (F05RelD Y (F05GoodPartial T none u) p)) hFC hAC hJC
  · intro t ht x hx
    have hInner := ((((hU.2.2.2.2.1 t (hTime ht)).fderivWithin hY (m := 1) (by norm_num)).differentiableOn
      (by norm_num) x (hSpace hx)).hasFDerivWithinAt)
    exact (L.hasFDerivAt.comp_hasFDerivWithinAt x hInner).mono hSpace
  · intro x hx t ht
    have hInner := (F05_good_time_spatial_jets hu htu (show (x,t) ∈ F05PosPatch ν T from ⟨hSpace hx,hTime ht⟩)).1
    exact (L.hasFDerivAt.comp_hasDerivWithinAt t hInner).mono hTime
  · exact hz

end Yau.Proofs.F05Aux
