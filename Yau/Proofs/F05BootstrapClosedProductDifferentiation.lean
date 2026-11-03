import Yau.Proofs.F05BootstrapProductDifferentiation
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Continuous actual spatial/time partial fields determine the genuine
joint within derivative on a closed convex product, including corners. -/

open Set Filter
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def F05ProductDerivative (A : E →L[ℝ] V) (J : V) : (E × ℝ) →L[ℝ] V :=
  A.comp (ContinuousLinearMap.fst ℝ E ℝ)+
    ((1 : ℝ →L[ℝ] ℝ).smulRight J).comp (ContinuousLinearMap.snd ℝ E ℝ)

theorem F05_closed_product_derivative {X : Set E} (hConv : Convex ℝ X)
    (hClosure : closure (interior X) = X) {s T : ℝ} (hsT : s < T)
    {F : E × ℝ → V} {A : E × ℝ → E →L[ℝ] V} {J : E × ℝ → V}
    (hF : ContinuousOn F (X ×ˢ Icc s T))
    (hA : ContinuousOn A (X ×ˢ Icc s T)) (hJ : ContinuousOn J (X ×ˢ Icc s T))
    (hSpatial : ∀ t ∈ Icc s T, ∀ x ∈ X, HasFDerivWithinAt (fun y => F (y,t)) (A (x,t)) X x)
    (hTime : ∀ x ∈ X, ∀ t ∈ Icc s T, HasDerivWithinAt (fun a => F (x,a)) (J (x,t)) (Icc s T) t)
    {p : E × ℝ} (hp : p ∈ X ×ˢ Icc s T) :
    HasFDerivWithinAt F (F05ProductDerivative (A p) (J p)) (X ×ˢ Icc s T) p := by
  let Q := X ×ˢ Icc s T
  let S := interior X ×ˢ Ioo s T
  let D : E × ℝ → (E × ℝ) →L[ℝ] V := fun z => F05ProductDerivative (A z) (J z)
  let L : V →L[ℝ] (ℝ →L[ℝ] V) := ContinuousLinearMap.smulRightL ℝ ℝ V (1 : ℝ →L[ℝ] ℝ)
  have hS : IsOpen S := isOpen_interior.prod isOpen_Ioo
  have hSub : S ⊆ Q := fun z hz => ⟨interior_subset hz.1,Ioo_subset_Icc_self hz.2⟩
  have hDC : ContinuousOn D Q :=
    (hA.clm_comp continuousOn_const).add
      ((L.continuous.comp_continuousOn hJ).clm_comp continuousOn_const)
  have hInterior (z : E × ℝ) (hz : z ∈ S) : HasFDerivAt F (D z) z := by
    apply F05_product_derivative_of_partial
    · filter_upwards [hS.mem_nhds hz] with q hq
      exact (hSpatial q.2 (Ioo_subset_Icc_self hq.2) q.1 (interior_subset hq.1)).hasFDerivAt
        (mem_of_superset (isOpen_interior.mem_nhds hq.1) interior_subset)
    · exact (hA z (hSub hz)).continuousAt (mem_of_superset (hS.mem_nhds hz) hSub)
    · exact (hTime z.1 (interior_subset hz.1) z.2 (Ioo_subset_Icc_self hz.2)).hasDerivAt
        (Icc_mem_nhds hz.2.1 hz.2.2)
  have hCl : closure S = Q := by
    dsimp only [S,Q]
    rw [closure_prod_eq,hClosure,closure_Ioo hsT.ne]
  change HasFDerivWithinAt F (D p) Q p
  rw [← hCl]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun z hz => (hInterior z hz).differentiableAt.differentiableWithinAt)
    (hConv.interior.prod (convex_Ioo s T)) hS
  · intro z hz
    rw [hCl] at hz
    exact (hF z hz).mono hSub
  · apply ((hDC p hp).mono hSub).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hInterior z hz).fderiv.symm

end Yau.Proofs.F05Aux
