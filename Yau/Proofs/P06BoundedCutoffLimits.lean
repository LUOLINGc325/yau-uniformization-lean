import Yau.Proofs.P06BoundedOrderAssemblyLimit
import Yau.Proofs.P06L2HeatExistence
import Yau.Proofs.P06HeatOrderBounds

noncomputable section
open MeasureTheory
open scoped Manifold Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ}

/-- Every original L² cutoff evolution obeys the same original C, with a
uniform norm bound independent of its cutoff index and of positive time. -/
theorem metricCutoff_l2Heat_order_norm (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (A : RealForm X.manifold 2) (hA : SmoothRealForm A) (h11 : RealOneOne A)
    {C : ℝ} (hC : 0 ≤ C) (hb : FormOrderBound X.metric.form C A)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (Us : ℕ → ℝ → RealForm X.manifold 2)
    (hUs : ∀ j, 1 ≤ j → IsL2FormHeat X.metric.form μ (fun x => χ j x • A x) (Us j)) :
    ∀ j, 1 ≤ j → ∀ t, 0 < t → FormOrderBound X.metric.form C (Us j t) ∧
      ∀ x, formNormSq X.metric.form (Us j t) x ≤ (n : ℝ) * C ^ 2 := by
  obtain ⟨D, hD, hcut⟩ := hχ
  have hfamily : MetricCutoffFamily X.metric.form o χ := ⟨D, hD, hcut⟩
  intro j hj t ht
  let Aj : RealForm X.manifold 2 := fun x => χ j x • A x
  have hAj : L2RealForm X.metric.form μ Aj :=
    metricCutoff_smooth_l2 X.metric μ hμ o χ hfamily A hA j hj
  have hAj11 : RealOneOne Aj := realOneOne_multiply (χ j) A h11
  have hbAj : FormOrderBound X.metric.form C Aj :=
    formOrderBound_multiply X.metric.form (χ j) (hcut j hj).2.2.1 A hC hb
  have hs : SmoothRealForm (Us j t) := by
    intro a I
    exact ((hUs j hj).2.2.1 a I).comp (contDiffOn_id.prodMk contDiffOn_const)
      (fun z hz => ⟨hz, ht⟩)
  have hL := (hUs j hj).2.2.2.2.1 t ht
  have he := L2HeatExistence.isL2FormHeat_realization X.metric μ hμ Aj hAj (Us j) (hUs j hj) ht
  have htype := hodgeHeat_smooth_representative_oneOne X.metric μ hμ X.kahler_metric
    Aj (Us j t) hAj hAj11 hs hL t ht.le he
  have horder := hodgeHeat_smooth_representative_order X.metric μ hμ X.kahler_metric
    (nonnegativeHBC X) Aj (Us j t) hAj hAj11 hC hbAj hs hL t ht.le he
  exact ⟨horder, fun x => G04Aux.norm_of_order X.metric.form (Us j t) htype hC horder x⟩

/-- The actual local smooth cutoff limit already has the required bounded
PDE class norm. This step assumes neither a heat class nor L² for the limit. -/
theorem boundedFormHeatClass_of_metricCutoff_limit (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (A : RealForm X.manifold 2) (hA : BoundedOneOneData X.metric.form A)
    (o : Pt X) (χ : ℕ → Pt X → ℝ) (hχ : MetricCutoffFamily X.metric.form o χ)
    (Us : ℕ → ℝ → RealForm X.manifold 2) (U : ℝ → RealForm X.manifold 2)
    (hUs : ∀ j, 1 ≤ j → IsL2FormHeat X.metric.form μ (fun x => χ j x • A x) (Us j))
    (hlim : FormHeatLocalSmoothLimit Us U) : BoundedFormHeatClass X.metric.form U := by
  obtain ⟨hsA, h11, C, hC, hb⟩ := hA
  have hcut := metricCutoff_l2Heat_order_norm X μ hμ A hsA h11 hC hb o χ hχ Us hUs
  have hnorm := BoundedOrder.formNormSq_bound_of_localSmoothLimit X.metric.form
    ((n : ℝ) * C ^ 2) Us U hlim (fun j hj t ht x => (hcut j hj t ht).2 x)
  intro T hT
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  refine ⟨((n : ℝ) + 1) * (C + 1), mul_pos (by linarith) (by linarith), ?_⟩
  intro x t ht htT
  calc
    _ ≤ (n : ℝ) * C ^ 2 := hnorm t ht x
    _ ≤ ((n : ℝ) + 1) ^ 2 * C ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (n : ℝ)]) (sq_nonneg C)
    _ ≤ ((n : ℝ) + 1) ^ 2 * (C + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg ((n : ℝ) + 1))
    _ = _ := by ring

end Yau.NodeProofs.P06Aux
