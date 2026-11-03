import Yau.Proofs.P06HeatPositiveTraceTests
import Yau.Proofs.P06CurrentConstants
import Yau.Proofs.P06DDbarHeatCurrent
import Yau.Proofs.P06HodgeRegularityHeatEquation
import Yau.Proofs.P06WeakDDbarCurrent

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03
variable {n : ℕ}

/-- The original weak upper constant survives the actual heat after
subtracting the compact-exterior constant. The test evolution is the
genuine Hodge heat, with positivity and its actual trace L¹ estimate. -/
theorem compactDifferenceHeat_current_upper (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (f : Pt X → ℝ) (C : ℝ) (hf : LipschitzForMetric X.metric.form f)
    (hc : ConstantOutsideCompact f) (hw : WeakLeviUpper X.metric.form f C)
    (c : ℝ) (hcont : Continuous (fun x => f x - c))
    (hcompact : HasCompactSupport (fun x => f x - c))
    (t : ℝ) (ht : 0 < t) (u : Pt X → ℝ) (hu : SmoothFn u)
    (huL : L2RealForm X.metric.form μ (G04Aux.scalarForm u))
    (huRep : realizeActualForm X.metric μ (G04Aux.scalarForm u) huL =
      hodgeHeatHilbert X.metric μ hμ 0 t (realizeActualForm X.metric μ
        (G04Aux.scalarForm (fun x => f x - c))
        (DDbarHeat.continuous_compact_scalar_l2 X.metric μ hμ (fun x => f x - c) hcont hcompact)))
    (B : RealForm X.manifold 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (h11 : RealOneOne B) (hp : FormLE 0 B) :
    (∫ x, formInner X.metric.form (G04Aux.ddRealForm u) B x ∂μ) ≤
      C * ∫ x, formTrace X.metric.form B x ∂μ := by
  let hBL := smooth_compactlySupported_l2RealForm X.metric μ hμ B hB hcB
  let b := realizeActualForm X.metric μ B hBL
  obtain ⟨V, hV, _, hVrep⟩ := hodgeStrongPath_geometric_regularity X.metric μ hμ
    (fun s => hodgeHeatHilbert X.metric μ hμ 2 s b)
    (hodgeHeatHilbert_strongPath X.metric μ hμ 2 b)
  obtain ⟨hVL, heV⟩ := hVrep t ht
  have hsV : SmoothRealForm (V t) := by
    intro a I
    exact (hV a I).comp (contDiffOn_id.prodMk contDiffOn_const) (fun z hz => ⟨hz, ht⟩)
  obtain ⟨η, hη, hcη, hηrange, hηone⟩ := exists_unitInterval_compact_smooth_one_near X.metric hcompact
  obtain ⟨hF, hcF, h11F, hpF, _, hmass⟩ := hodgeHeat_localized_positive_test
    X.metric μ hμ X.kahler_metric (nonnegativeHBC X) B (V t) hB hcB h11 hp hsV hVL t ht.le heV
    η hη hcη hηrange
  have hC : 0 ≤ C := weakLeviUpper_constantOutside_nonnegative X.metric f C hc hw
  calc
    _ = ∫ x, (f x - c) * WeakCurrent.ddAdjointScalar X.metric.form (multiplyRealForm η (V t)) x ∂μ :=
      DDbarHeat.dd_heat_current_compact X.metric μ hμ X.kahler_metric
        (fun x => f x - c) hcont hcompact B hB hcB t ht u hu (V t) hsV huL hVL huRep heV η hη hcη hηone
    _ = ∫ x, f x * WeakCurrent.ddAdjointScalar X.metric.form (multiplyRealForm η (V t)) x ∂μ :=
      current_pairing_sub_constant X.metric μ hμ f (continuous_of_metricLipschitz X.metric hf)
        c _ hF hcF
    _ ≤ C * ∫ x, formTrace X.metric.form (multiplyRealForm η (V t)) x ∂μ :=
      WeakCurrent.weakLeviUpper_lipschitz_global_test X.metric μ hμ f hf C hc hw _ hF hcF h11F hpF
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hC

end Yau.NodeProofs.P06Aux
