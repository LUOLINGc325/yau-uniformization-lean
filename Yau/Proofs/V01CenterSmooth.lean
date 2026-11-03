import spec.CHAIN.CONTRACTS

/-! The actual open-neighborhood smoothness in StrictEnvelopeContact applies
to every admissible center. This does not infer a common smooth neighborhood
from the original pointwise smooth germ. -/

noncomputable section
open Set
open scoped Topology ContDiff
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem admissible_center_in_chart
    {d : VariationData X q} {j : ℕ} {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    InCotangentTimeChart d.chart (F.f 0) F.s (centerCylinder d) :=
  hF.2.2.2.2.2.1

theorem center_test_contDiffAt
    {d : VariationData X q} (hContact : StrictEnvelopeContact d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    ContDiffAt ℝ 2 (fun z => d.test (cotangentChartInv d.chart z) F.s)
      (cotangentChart d.chart (F.f 0)) := by
  have hCenter := admissible_center_in_chart hF
  obtain ⟨V, hV, hKV, _hVD, hSmooth⟩ := hContact.2.2.2.2.2.2
  have hp : (cotangentChart d.chart (F.f 0), F.s) ∈ V := hKV hCenter.2
  have hAt := hSmooth.contDiffAt (hV.mem_nhds hp)
  have hSlice : ContDiffAt ℝ ∞ (fun z : CotangentCoord n => (z, F.s))
      (cotangentChart d.chart (F.f 0)) := by fun_prop
  have hAt₂ : ContDiffAt ℝ 2
      (fun p : CotangentCoord n × ℝ => d.test (cotangentChartInv d.chart p.1) p.2)
      (cotangentChart d.chart (F.f 0), F.s) := hAt.of_le (by norm_num)
  have hSlice₂ : ContDiffAt ℝ 2 (fun z : CotangentCoord n => (z, F.s))
      (cotangentChart d.chart (F.f 0)) := hSlice.of_le (by norm_num)
  exact hAt₂.comp (cotangentChart d.chart (F.f 0)) hSlice₂

end Yau.Blueprint.V01Proof
