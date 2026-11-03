import Yau.Proofs.V03Elementary
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Continuity of parameter integrals from actual joint continuity on a
compact neighborhood, with the domination bound derived by compactness. -/

open scoped Topology
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint.V03Proof

variable {P F : Type*} [NormedAddCommGroup P]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuousAt_intervalIntegral_of_joint_compact
    {K : Set P} (hK : IsCompact K) {x : P} (hx : K ∈ 𝓝 x)
    {a b : ℝ} {f : P → ℝ → F}
    (hf : ContinuousOn (fun p : P × ℝ => f p.1 p.2) (K ×ˢ Set.uIcc a b)) :
    ContinuousAt (fun y => ∫ t in a..b, f y t) x := by
  have htime : ∀ y ∈ K, ContinuousOn (f y) (Set.uIcc a b) := by
    intro y hy
    exact hf.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht => ⟨hy, ht⟩)
  have hparam : ∀ t ∈ Set.uIcc a b, ContinuousAt (fun y => f y t) x := by
    intro t ht
    have hc : ContinuousOn (fun y => f y t) K :=
      hf.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun y hy => ⟨hy, ht⟩)
    exact hc.continuousAt hx
  obtain ⟨C, hC⟩ :=
    ((hK.prod (isCompact_uIcc : IsCompact (Set.uIcc a b))).image_of_continuousOn hf).isBounded.exists_norm_le
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C)
  · filter_upwards [hx] with y hy
    exact ((htime y hy).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [hx] with y hy
    exact Eventually.of_forall fun t ht =>
      hC (f y t) ⟨(y, t), ⟨hy, Set.uIoc_subset_uIcc ht⟩, rfl⟩
  · exact intervalIntegrable_const
  · exact Eventually.of_forall fun t ht => hparam t (Set.uIoc_subset_uIcc ht)

end Yau.Blueprint.V03Proof
