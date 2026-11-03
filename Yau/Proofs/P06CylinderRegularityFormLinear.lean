import Yau.Proofs.P06CylinderRegularityHodgeEquation

/-! Differences of actual smooth original form heat solutions satisfy
the same original equation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau Yau.Blueprint Yau.LeafProofs.L03

theorem formHeatEquation_sub {n k : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {U V : ℝ → RealForm M k} (hUs : SmoothFormTime U (Set.Ioi 0))
    (hVs : SmoothFormTime V (Set.Ioi 0))
    (hU : FormHeatEquation g.form U) (hV : FormHeatEquation g.form V) :
    FormHeatEquation g.form (fun t => U t-V t) := by
  intro x z hz t ht I
  have hA := smoothFormTime_slice hUs ht
  have hB := smoothFormTime_slice hVs ht
  have hD : SmoothRealForm (U t-V t) := (smoothFormSubmodule (M := M) k).sub_mem hA hB
  have hHodge : hodgeRealForm g.form k (U t-V t) =
      hodgeRealForm g.form k (U t)-hodgeRealForm g.form k (V t) := by
    have he : U t-V t = U t+(-1 : ℝ) • V t := by rw [neg_one_smul ℝ (V t),sub_eq_add_neg]
    rw [he,hodgeRealForm_add g μ hμ _ _ hA (smoothRealForm_smul _ _ hB),
      hodgeRealForm_smul g μ hμ _ _ hB,
      neg_one_smul ℝ (hodgeRealForm g.form k (V t)),sub_eq_add_neg]
  have hRepD := hodgeRealForm_represents g μ hμ (U t-V t) hD x z hz I
  have hRepU := hodgeRealForm_represents g μ hμ (U t) hA x z hz I
  have hRepV := hodgeRealForm_represents g μ hμ (V t) hB x z hz I
  have h := (hU x z hz t ht I).sub (hV x z hz t ht I)
  have hGenerator : hodgeGeneratorComponents g.form x (formComponents (U t-V t) x) z I =
      hodgeGeneratorComponents g.form x (formComponents (U t) x) z I-
        hodgeGeneratorComponents g.form x (formComponents (V t) x) z I := by
    unfold hodgeGeneratorComponents
    rw [← hRepD,hHodge]
    change -(formComponents (hodgeRealForm g.form k (U t)) x z I-
      formComponents (hodgeRealForm g.form k (V t)) x z I)/2 = _
    rw [hRepU,hRepV]
    ring
  rw [hGenerator]
  exact h

theorem smoothFormTime_sub {n k : ℕ} {M : ComplexManifold n}
    {U V : ℝ → RealForm M k} (hU : SmoothFormTime U (Set.Ioi 0))
    (hV : SmoothFormTime V (Set.Ioi 0)) :
    SmoothFormTime (fun t => U t-V t) (Set.Ioi 0) := by
  intro x I
  exact (hU x I).sub (hV x I)

end Yau.NodeProofs.P06Aux.CylinderReg
