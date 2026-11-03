import Yau.Proofs.P06BoundedOrderAssemblyLimit
import Yau.Proofs.P06HeatOrderBounds
import Yau.Proofs.P06L2HeatExistence
import Yau.Proofs.P06CutoffOrder
import Yau.Proofs.P06Geometry

/-! Original L² heat order and the same bounds for arbitrary cutoff limits. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux.BoundedOrder
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ} {M : ComplexManifold n}

theorem formLE_multiply_nonnegative_pair (η : M.Carrier → ℝ)
    (hη : ∀ x, 0 ≤ η x) (A B : RealForm M 2) (hAB : FormLE A B) :
    FormLE (multiplyRealForm η A) (multiplyRealForm η B) := by
  intro x
  rw [formHermitianMatrix_multiply, formHermitianMatrix_multiply, ← smul_sub]
  exact (hAB x).smul (Complex.nonneg_iff.mpr ⟨hη x, rfl⟩)

theorem metricCutoff_range (g : HermitianField M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) (hχ : MetricCutoffFamily g o χ) :
    ∀ j, 1 ≤ j → ∀ x, χ j x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨c, hc, hcut⟩ := hχ
  exact fun j hj => (hcut j hj).2.2.1

theorem l2FormHeat_orderBound (X : KahlerManifold n) (μ : Measure X.manifold.Carrier)
    (hμ : IsRiemannianVolume X.metric.form μ) (A : RealForm X.manifold 2)
    (U : ℝ → RealForm X.manifold 2) (h11 : RealOneOne A)
    {C : ℝ} (hC : 0 ≤ C) (hbound : FormOrderBound X.metric.form C A)
    (hU : IsL2FormHeat X.metric.form μ A U) :
    ∀ t, 0 < t → FormOrderBound X.metric.form C (U t) := by
  intro t ht
  exact hodgeHeat_smooth_representative_order X.metric μ hμ X.kahler_metric (nonnegativeHBC X)
    A (U t) hU.1 h11 hC hbound (smoothFormTime_slice hU.2.2.1 ht)
    (hU.2.2.2.2.1 t ht) t ht.le
    (L2HeatExistence.isL2FormHeat_realization X.metric μ hμ A hU.1 U hU ht)

theorem l2FormHeat_comparison (X : KahlerManifold n) (μ : Measure X.manifold.Carrier)
    (hμ : IsRiemannianVolume X.metric.form μ) (A B : RealForm X.manifold 2)
    (U V : ℝ → RealForm X.manifold 2) (h11A : RealOneOne A) (h11B : RealOneOne B)
    (hU : IsL2FormHeat X.metric.form μ A U) (hV : IsL2FormHeat X.metric.form μ B V)
    (hAB : FormLE A B) : ∀ t, 0 < t → FormLE (U t) (V t) := by
  intro t ht
  exact hodgeHeat_smooth_representatives_comparison X.metric μ hμ X.kahler_metric (nonnegativeHBC X)
    A B (U t) (V t) hU.1 hV.1 h11A h11B hAB
    (smoothFormTime_slice hU.2.2.1 ht) (hU.2.2.2.2.1 t ht)
    (smoothFormTime_slice hV.2.2.1 ht) (hV.2.2.2.2.1 t ht) t ht.le
    (L2HeatExistence.isL2FormHeat_realization X.metric μ hμ A hU.1 U hU ht)
    (L2HeatExistence.isL2FormHeat_realization X.metric μ hμ B hV.1 V hV ht)

theorem boundedFormHeat_orderBound_of_cutoffConstruction
    (X : KahlerManifold n) (μ : Measure X.manifold.Carrier)
    (hμ : IsRiemannianVolume X.metric.form μ) (hc : HodgeCutoffConstruction X.metric.form μ)
    (A : RealForm X.manifold 2) (U : ℝ → RealForm X.manifold 2)
    (hA : BoundedOneOneData X.metric.form A) (hU : IsBoundedFormHeat X.metric.form A U)
    {C : ℝ} (hC : 0 ≤ C) (hbound : FormOrderBound X.metric.form C A) :
    ∀ t, 0 < t → FormOrderBound X.metric.form C (U t) := by
  obtain ⟨V, hV, hcut⟩ := hc.2 A hA
  obtain ⟨o⟩ := (inferInstance : Nonempty X.manifold.Carrier)
  obtain ⟨χ, hχ⟩ := hc.1 o
  obtain ⟨hcutL2, ⟨Us, hUs⟩, hlimit⟩ := hcut o χ hχ
  have hbounds : ∀ j, 1 ≤ j → ∀ t, 0 < t → FormOrderBound X.metric.form C (Us j t) := by
    intro j hj
    exact l2FormHeat_orderBound X μ hμ _ (Us j) (realOneOne_multiply (χ j) A hA.2.1) hC
      (formOrderBound_multiply X.metric.form (χ j) (metricCutoff_range _ o χ hχ j hj) A hC hbound)
      (hUs j hj)
  have hb := formOrderBound_of_localSmoothLimit X.metric.form C Us V (hlimit Us hUs) hbounds
  intro t ht
  rw [boundedFormHeat_unique X A U V hU hV t ht.le]
  exact hb t ht

theorem boundedFormHeat_comparison_of_cutoffConstruction
    (X : KahlerManifold n) (μ : Measure X.manifold.Carrier)
    (hμ : IsRiemannianVolume X.metric.form μ) (hc : HodgeCutoffConstruction X.metric.form μ)
    (A B : RealForm X.manifold 2) (U V : ℝ → RealForm X.manifold 2)
    (hA : BoundedOneOneData X.metric.form A) (hB : BoundedOneOneData X.metric.form B)
    (hU : IsBoundedFormHeat X.metric.form A U) (hV : IsBoundedFormHeat X.metric.form B V)
    (hAB : FormLE A B) : ∀ t, 0 < t → FormLE (U t) (V t) := by
  obtain ⟨UA, hUA, hcutA⟩ := hc.2 A hA
  obtain ⟨VB, hVB, hcutB⟩ := hc.2 B hB
  obtain ⟨o⟩ := (inferInstance : Nonempty X.manifold.Carrier)
  obtain ⟨χ, hχ⟩ := hc.1 o
  obtain ⟨hcutAL2, ⟨Us, hUs⟩, hlimitA⟩ := hcutA o χ hχ
  obtain ⟨hcutBL2, ⟨Vs, hVs⟩, hlimitB⟩ := hcutB o χ hχ
  have horders : ∀ j, 1 ≤ j → ∀ t, 0 < t → FormLE (Us j t) (Vs j t) := by
    intro j hj
    exact l2FormHeat_comparison X μ hμ _ _ (Us j) (Vs j)
      (realOneOne_multiply (χ j) A hA.2.1) (realOneOne_multiply (χ j) B hB.2.1)
      (hUs j hj) (hVs j hj)
      (formLE_multiply_nonnegative_pair (χ j)
        (fun x => (metricCutoff_range _ o χ hχ j hj x).1) A B hAB)
  have ho := formLE_of_localSmoothLimits Us Vs UA VB (hlimitA Us hUs) (hlimitB Vs hVs) horders
  intro t ht
  rw [boundedFormHeat_unique X A U UA hU hUA t ht.le,
    boundedFormHeat_unique X B V VB hV hVB t ht.le]
  exact ho t ht

end Yau.NodeProofs.P06Aux.BoundedOrder
