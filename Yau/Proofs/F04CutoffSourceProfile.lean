import Yau.Proofs.F04FlowSourceSmooth
import Yau.Proofs.F03ScalarL2Pairing

open MeasureTheory Set Filter
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.HeatConcreteBindings Yau.Proofs.F03Aux

/-- The genuine cutoff source has an actual fixed-pivot L2 path and
 actual physical source representatives for ALL times via the existing
 clamp. Its original nonnegative source bound is proved, not supplied. -/
theorem flow_cutoff_source_L2_profile
    {n : ℕ} (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (Ω K : Set (Pt X)) (hΩ : MeasurableSet Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    {S : ℝ} (hS : 0 < S) (q : Pt X → ℝ) (hq : SmoothFn q)
    (hqRange : ∀ x, 0 ≤ q x ∧ q x ≤ 1) :
    ∃ hv : ∀ t, ScalarL2 (μ.restrict Ω) (fun x => q x * source X h x (timeClamp S hS.le t)),
      Continuous (fun t => scalarToLp (hv t)) ∧
      MemLp (fun t => scalarToLp (hv t)) 2 (volume.restrict (Ioo 0 S)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 S), ∀ᵐ x ∂μ.restrict Ω,
        0 ≤ scalarToLp (hv t) x ∧ scalarToLp (hv t) x ≤ source X h x t := by
  have hF := flow_cutoff_source_smooth_closed X o h U P ρ hloc hS q hq
  obtain ⟨hf,hc⟩ := compact_scalar_profile_L2 X.metric μ hμ Ω K hΩ hK hΩK hS.le
    (fun x t => q x * source X h x t) (smoothSpaceTime_continuousOn hF)
  let hv : ∀ t, ScalarL2 (μ.restrict Ω) (fun x => q x * source X h x (timeClamp S hS.le t)) :=
    fun t => (scalarL2_iff_memLp _ _).mpr (hf t)
  have hCT : Continuous (fun t => scalarToLp (hv t)) := hc
  refine ⟨hv,hCT,?_,?_⟩
  · exact (Yau.LeafProofs.L16HilbertTimeRegularization.continuousOn_memLp_two hCT.continuousOn).mono_measure
      (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    filter_upwards [(hf t).coeFn_toLp] with x hx
    change 0 ≤ (hf t).toLp _ x ∧ (hf t).toLp _ x ≤ source X h x t
    rw [hx,timeClamp_eq_of_mem S hS.le (Ioo_subset_Icc_self ht)]
    have hn : 0 ≤ source X h x t := source_nonneg o h U P ρ hloc x t ht.1.le
    exact ⟨mul_nonneg (hqRange x).1 hn,by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hqRange x).2 hn⟩

end Yau.F04Proof
