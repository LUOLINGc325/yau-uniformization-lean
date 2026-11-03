import Yau.Proofs.P06CylinderRegularityOriginalFamilies
import Yau.Proofs.P06LocalCauchyLimitPDE

/-! The actual positive-time heat limit, independent of every cutoff,
basepoint, and original L² heat evolution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.LeafProofs.L03

theorem exists_form_cutoff_positive_heat {n : ℕ} (X : KahlerManifold n)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (A : RealForm X.manifold 2) (hA : SmoothRealForm A)
    (B : ℝ) (hb : ∀ x, formNormSq X.metric.form A x ≤ B^2) :
    ∃ U : ℝ → RealForm X.manifold 2, U 0=A ∧ SmoothFormTime U (Set.Ioi 0) ∧
      FormHeatEquation X.metric.form U ∧
      ∀ o χ, MetricCutoffFamily X.metric.form o χ →
        ∀ Vs : ℕ → ℝ → RealForm X.manifold 2,
          (∀ j, 1 ≤ j → IsL2FormHeat X.metric.form μ (fun x => χ j x • A x) (Vs j)) →
          FormHeatLocalSmoothLimit Vs U := by
  classical
  let o : Pt X := Classical.arbitrary _
  obtain ⟨χ,hχ⟩ := metricCutoffFamily X.metric o
  obtain ⟨Us,U,hUs,hzero,hU,hLimit⟩ := exists_canonical_cutoff_positive_limit X μ hμ o χ hχ A hA B hb
  have hPDE := LocalCauchyLimit.formHeatEquation_limit X.metric μ hμ Us U
    (fun j => (hUs j).2.1) hU hLimit (fun j => (hUs j).2.2.1)
  refine ⟨U,hzero,hU,hPDE,?_⟩
  intro o' χ' hχ' Vs hVs
  exact original_cutoff_jointJetLimit X μ hμ o χ hχ A hA B hb Us hUs U hU hLimit o' χ' hχ' Vs hVs

end Yau.NodeProofs.P06Aux.CylinderReg
