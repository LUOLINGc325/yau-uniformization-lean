import Yau.Proofs.V03EnvelopeSelection
import Yau.Proofs.V03FixedDiscWalls

/-! Selection from the actual raw disc infimum, with an interior center.
The raw class is exactly the original smooth closed-disc class. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem contact_raw_almost_minimizer {d : VariationData X q} (hd : VariationSetup d)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : VariationDisc X, CotangentDisc F.f ∧
      ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1) ∧ F.w 0 = 0 ∧
      0 < F.s ∧ F.s < d.T ∧
      InCotangentTimeChart d.chart (F.f 0) F.s (interior (centerCylinder d)) ∧
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, discTime F ζ < d.T) ∧
      circleAverage (fun θ => let y := F.f (circlePoint θ)
        dualNorm (d.h (discTime F (circlePoint θ))) y.1 y.2) - d.test (F.f 0) F.s < η := by
  have hc := hd.2.2.2.2.2.2.2.1
  have hcC : d.contact ∈ centerCylinder d := interior_subset hc.2.1
  let assoc : ComplexVector n × ComplexVector n × ℝ → CotangentCoord n × ℝ :=
    fun p => ((p.1, p.2.1), p.2.2)
  let c : ComplexVector n × ComplexVector n × ℝ :=
    (d.contact.1.1, d.contact.1.2, d.contact.2)
  have hac : assoc c = d.contact := rfl
  have hassoc : Continuous assoc :=
    (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)
  let φ : ComplexVector n × ComplexVector n × ℝ → ℝ :=
    fun p => d.test (cotangentChartInv d.chart (assoc p).1) (assoc p).2
  let S : Set (ComplexVector n × ComplexVector n × ℝ) :=
    {p | p.1 ∈ chartTarget d.chart ∧ 0 < p.2.2 ∧ p.2.2 < d.T}
  have hφ : ContinuousAt φ c := by
    obtain ⟨V, hV, hCV, _, htest⟩ := hc.2.2.2.2.2.2
    have htestAt : ContinuousAt
        (fun x : CotangentCoord n × ℝ => d.test (cotangentChartInv d.chart x.1) x.2)
        (assoc c) := htest.continuousOn.continuousAt (hV.mem_nhds (hCV hcC))
    exact htestAt.comp (f := assoc) hassoc.continuousAt
  have heq : liminf (envelopeRawChart d.h d.T d.chart) (𝓝[S] c) = (φ c : EReal) := by
    exact ((hc.2.2.2.2.1 d.contact hcC).mpr rfl).symm
  have hU : assoc ⁻¹' interior (centerCylinder d) ∈ 𝓝[S] c := by
    exact mem_inf_of_left (hassoc.continuousAt (isOpen_interior.mem_nhds hc.2.1))
  obtain ⟨p, hp, hpraw⟩ := exists_near_liminf_contact heq hφ.continuousWithinAt hU hη
  obtain ⟨f, hf⟩ := iInf_lt_iff.mp hpraw
  obtain ⟨ξd, hξd⟩ := iInf_lt_iff.mp hf
  obtain ⟨w, hw⟩ := iInf_lt_iff.mp hξd
  obtain ⟨ha, havg⟩ := iInf_lt_iff.mp hw
  let F : VariationDisc X := { f := fun ζ => (f ζ, ξd ζ), w := w, s := p.2.2 }
  have hcenter : F.f 0 = cotangentChartInv d.chart (p.1, p.2.1) := by
    exact Prod.ext ha.2.2.2.2.1 ha.2.2.2.2.2.1
  have htarget : (p.1, p.2.1) ∈ cotangentTarget d.chart := ⟨hp.2.1, Set.mem_univ _⟩
  have hchart : InCotangentTimeChart d.chart (F.f 0) F.s (interior (centerCylinder d)) := by
    rw [hcenter]
    refine ⟨cotangentChartInv_mapsTo d.chart htarget, ?_⟩
    change (cotangentChart d.chart (cotangentChartInv d.chart (p.1, p.2.1)), p.2.2) ∈ _
    rw [cotangentChart_right_inv d.chart htarget]
    exact hp.1
  refine ⟨F, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.2.2.1, ha.1, ha.2.1, hchart,
    ha.2.2.2.2.2.2.2, ?_⟩
  have havgR := EReal.coe_lt_coe_iff.mp havg
  have htest : d.test (F.f 0) F.s = φ p := by rw [hcenter]
  change circleAverage (fun θ =>
    dualNorm (d.h (p.2.2 * Real.exp (2 * (w (circlePoint θ)).re)))
      (f (circlePoint θ)) (ξd (circlePoint θ))) - d.test (F.f 0) F.s < η
  rw [htest]
  apply sub_lt_iff_lt_add.mpr
  simpa only [circlePoint, add_comm] using havgR

end Yau.Blueprint.V03Proof
