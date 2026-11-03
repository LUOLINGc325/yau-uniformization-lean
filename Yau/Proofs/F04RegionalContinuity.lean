import Yau.Proofs.F04ChartContinuity
import Yau.LeafProofs.L18

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof

/-- Actual regional chart continuity transports to the physical product,
 including arbitrary closed time faces. -/
theorem chartwise_regional_continuousOn
    {n : ℕ} {M : ComplexManifold n} {Ω : Set M.Carrier} {I : Set ℝ}
    {v : M.Carrier → ℝ → ℝ}
    (hv : ∀ c, ContinuousOn (fun p : ComplexVector n × ℝ => v (chartInv c p.1) p.2)
      ((chartTarget c ∩ chartInv c ⁻¹' Ω) ×ˢ I)) :
    ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (Ω ×ˢ I) := by
  rintro ⟨x,t⟩ hp
  have hx : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hcz := Yau.LeafProofs.chartInv_chartPt_of_mem x x (mem_chart_source _ _)
  have hmapc : ContinuousAt (fun p : M.Carrier × ℝ => (chartPt x p.1,p.2)) (x,t) :=
    ((continuousAt_extChartAt (I := ComplexModel n) x).comp continuousAt_fst).prodMk continuousAt_snd
  have hnear : ∀ᶠ p : M.Carrier × ℝ in 𝓝[Ω ×ˢ I] (x,t),
      p.1 ∈ (extChartAt (ComplexModel n) x).source := by
    apply nhdsWithin_le_nhds
    exact continuousAt_fst.eventually
      ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds (mem_extChartAt_source x))
  have hmap : Tendsto (fun p : M.Carrier × ℝ => (chartPt x p.1,p.2))
      (𝓝[Ω ×ˢ I] (x,t)) (𝓝[(chartTarget x ∩ chartInv x ⁻¹' Ω) ×ˢ I] (chartPt x x,t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hmapc.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [hnear,self_mem_nhdsWithin] with p hpx hpt
    refine ⟨⟨(extChartAt (ComplexModel n) x).map_source hpx,?_⟩,hpt.2⟩
    change chartInv x (chartPt x p.1) ∈ Ω
    have hi : chartInv x (chartPt x p.1) = p.1 := (extChartAt (ComplexModel n) x).left_inv hpx
    rw [hi]
    exact hpt.1
  have hcomp := (hv x (chartPt x x,t) ⟨⟨hx,by
    change chartInv x (chartPt x x) ∈ Ω
    rw [hcz]
    exact hp.1⟩,hp.2⟩).tendsto.comp hmap
  have heq : (fun p : M.Carrier × ℝ => v (chartInv x (chartPt x p.1)) p.2)
      =ᶠ[𝓝[Ω ×ˢ I] (x,t)] (fun p => v p.1 p.2) := by
    filter_upwards [hnear] with p hpx
    exact congrArg (fun y => v y p.2) ((extChartAt (ComplexModel n) x).left_inv hpx)
  have hh := (tendsto_congr' heq).mp hcomp
  change Tendsto (fun p : M.Carrier × ℝ => v p.1 p.2) (𝓝[Ω ×ˢ I] (x,t)) (𝓝 (v x t))
  simpa only [hcz] using hh

/-- Actual regional smooth profiles are physically continuous at every
 point of every supplied time face. -/
theorem smooth_regional_continuousOn
    {n : ℕ} {M : ComplexManifold n} {Ω : Set M.Carrier} {I : Set ℝ}
    {v : M.Carrier → ℝ → ℝ}
    (hv : ∀ c, ContDiffOn ℝ ∞ (fun p : Yau.Parabolic.Point n => v (chartInv c p.1) p.2)
      ((chartTarget c ∩ chartInv c ⁻¹' Ω) ×ˢ I)) :
    ContinuousOn (fun p : M.Carrier × ℝ => v p.1 p.2) (Ω ×ˢ I) :=
  chartwise_regional_continuousOn (fun c => (hv c).continuousOn)

/-- Actual Riemannian-volume almost-everywhere order between continuous
 physical functions holds at every point of an open spatial domain. -/
theorem physical_continuousOn_le_of_ae_le
    {n : ℕ} {M : ComplexManifold n} (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {Ω : Set M.Carrier} (hΩ : IsOpen Ω) {f k : M.Carrier → ℝ}
    (hf : ContinuousOn f Ω) (hk : ContinuousOn k Ω) (hfk : f ≤ᵐ[μ.restrict Ω] k) :
    ∀ x ∈ Ω, f x ≤ k x := by
  let : μ.IsOpenPosMeasure := Yau.LeafProofs.L18Aux.riemannianVolume_isOpenPosMeasure g μ hμ
  have hAE : (fun x => |k x-f x|) =ᵐ[μ.restrict Ω] (fun x => k x-f x) := by
    filter_upwards [hfk] with x hx
    exact abs_of_nonneg (sub_nonneg.mpr hx)
  have hEq := Measure.eqOn_open_of_ae_eq hAE hΩ (hk.sub hf).abs (hk.sub hf)
  intro x hx
  exact sub_nonneg.mp (abs_eq_self.mp (hEq hx))

end Yau.F04Proof
