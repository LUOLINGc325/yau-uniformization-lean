import Yau.Proofs.F01SpatialWordCalculus

/-! Spatial differentiation commutes exactly with the actual forward
zero extension. All spatial slices are smooth on the entire extended
slab even though no joint higher time regularity is asserted at zero. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatialDerivativeWord_forwardZeroSpaceTime (f : E × ℝ → F) (vs : List E) :
    spatialDerivativeWord vs (forwardZeroSpaceTime f) =
      forwardZeroSpaceTime (spatialDerivativeWord vs f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext p
    change fderiv ℝ (fun z => spatialDerivativeWord vs (forwardZeroSpaceTime f) (z, p.2)) p.1 v = _
    rw [ih]
    by_cases ht : p.2 ≤ 0
    · simp only [forwardZeroSpaceTime, forwardZeroExtension, if_pos ht, fderiv_const_apply,
        ContinuousLinearMap.zero_apply]
    · simp only [forwardZeroSpaceTime, forwardZeroExtension, if_neg ht]
      rfl

theorem forwardZeroSpaceTime_smooth_slices {f : E × ℝ → F} {S : Set E} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, ContDiffOn ℝ ∞ (fun x => f (x, t)) S)
    {t : ℝ} (htT : t ≤ T) :
    ContDiffOn ℝ ∞ (fun x => forwardZeroSpaceTime f (x, t)) S := by
  by_cases ht : t ≤ 0
  · have he : (fun x => forwardZeroSpaceTime f (x, t)) = fun _ => (0 : F) := by
      funext x
      exact forwardZeroExtension_eq_of_nonpos _ ht
    rw [he]
    exact contDiffOn_const
  · have he : (fun x => forwardZeroSpaceTime f (x, t)) = fun x => f (x, t) := by
      funext x
      exact if_neg ht
    rw [he]
    exact hf t ⟨(lt_of_not_ge ht).le, htT⟩

end Yau.NodeProofs.F01Aux
