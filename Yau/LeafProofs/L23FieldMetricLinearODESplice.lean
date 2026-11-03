import Yau.LeafProofs.L23FieldMetricLinearODEUniform

/-! Matching first jets splice actual linear differential-equation solutions. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 600000

theorem hasDerivAt_splice (f g : ℝ → E) (T : ℝ) (v : E)
    (heq : f T = g T) (hf : HasDerivAt f v T) (hg : HasDerivAt g v T) :
    HasDerivAt (fun t => if t ≤ T then f t else g t) v T := by
  let W : ℝ → E := fun t => if t ≤ T then f t else g t
  have HL : HasDerivWithinAt W v (Set.Iic T) T := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      exact if_pos ht
    · exact if_pos le_rfl
  have HR : HasDerivWithinAt W v (Set.Ici T) T := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      by_cases hle : t ≤ T
      · have hteq : t = T := le_antisymm hle ht
        subst t
        simpa only [W,if_pos le_rfl] using heq
      · exact if_neg hle
    · simpa only [W,if_pos le_rfl] using heq
  have H := HL.union HR
  rw [Set.Iic_union_Ici] at H
  exact H.hasDerivAt (by simp)

theorem linearODE_splice_hasDerivAt
    (A f g : ℝ → E →L[ℝ] E) (a b c d T : ℝ)
    (hf : ∀ t ∈ Set.Ioo a b, HasDerivAt f ((A t).comp (f t)) t)
    (hg : ∀ t ∈ Set.Ioo c d, HasDerivAt g ((A t).comp (g t)) t)
    (hfT : T ∈ Set.Ioo a b) (hgT : T ∈ Set.Ioo c d) (heq : f T = g T) :
    ∀ t ∈ Set.Ioo a d, HasDerivAt (fun u => if u ≤ T then f u else g u)
      ((A t).comp (if t ≤ T then f t else g t)) t := by
  intro t ht
  by_cases htT : t < T
  · have H := hf t ⟨ht.1,htT.trans hfT.2⟩
    have hEq : (fun u => if u ≤ T then f u else g u) =ᶠ[𝓝 t] f := by
      filter_upwards [Iio_mem_nhds htT] with u hu
      exact if_pos hu.le
    rw [if_pos htT.le]
    exact H.congr_of_eventuallyEq hEq
  · by_cases hTt : T < t
    · have H := hg t ⟨hgT.1.trans hTt,ht.2⟩
      have hEq : (fun u => if u ≤ T then f u else g u) =ᶠ[𝓝 t] g := by
        filter_upwards [Ioi_mem_nhds hTt] with u hu
        exact if_neg (not_le.mpr hu)
      rw [if_neg (not_le.mpr hTt)]
      exact H.congr_of_eventuallyEq hEq
    · have htEq : t = T := le_antisymm (le_of_not_gt hTt) (le_of_not_gt htT)
      subst t
      have HG := hg T hgT
      rw [← heq] at HG
      simpa only [if_pos le_rfl] using hasDerivAt_splice f g T ((A T).comp (f T)) heq (hf T hfT) HG

end Yau.LeafProofs.L23Aux
