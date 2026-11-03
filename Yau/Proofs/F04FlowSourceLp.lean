import Yau.Proofs.F04SpaceTimeLaplacian
import Yau.Proofs.F04FlowRhoLp
import Yau.Proofs.F04SourcePositive
import Yau.LeafProofs.L16HilbertTimeRegularization

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ}

/-- The actual source is jointly continuous on the original closed slab,
 using the source equation and the genuine physical derivative of rho. -/
theorem flow_source_continuousOn_closed
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {T : ℝ} (hT : 0 < T) :
    ContinuousOn (fun p : Pt X × ℝ => source X h p.1 p.2) (univ ×ˢ Icc 0 T) := by
  have hh : MetricFamilySmooth h (Icc 0 T) := fun c i j =>
    (hloc.1.2.1 c i j).mono (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hρ : SmoothSpaceTime ρ (Icc 0 T) := fun c => (hloc.2.2.2.1 c).mono
    (prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hLap := smoothSpaceTime_continuousOn (metricFamily_laplacian_spaceTime_smooth h hT hh hρ)
  have hR := flow_scalarCurvature_continuousOn_closed X o h U P ρ hloc hT
  apply (hR.sub hLap).congr
  intro p hp
  have he := rho_source_equation o h U P ρ hloc T hT p.1 p.2 hp.2
  unfold heatOp at he
  rw [rho_derivWithin_Icc o h U P ρ hloc T hT p.1 p.2 hp.2] at he
  exact he.symm

/-- A compact actual domain gives a genuine nonnegative L2 source curve in
 the fixed initial-volume pivot, with strong physical-time continuity. -/
theorem flow_source_L2_profile
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ)
    (O K : Set (Pt X)) (hO : MeasurableSet O) (hK : IsCompact K) (hOK : O ⊆ K)
    {T : ℝ} (hT : 0 < T) :
    ∃ hf : ∀ t : ℝ, MemLp (fun x => source X h x (timeClamp T hT.le t)) 2 (μ.restrict O),
      Continuous (fun t => (hf t).toLp (fun x => source X h x (timeClamp T hT.le t))) ∧
      MemLp (fun t => (hf t).toLp (fun x => source X h x (timeClamp T hT.le t))) 2
        (volume.restrict (Ioo 0 T)) ∧
      ∀ t : ℝ, ∀ᵐ x ∂μ.restrict O,
        0 ≤ ((hf t).toLp (fun x => source X h x (timeClamp T hT.le t))) x := by
  obtain ⟨hf, hc⟩ := compact_scalar_profile_L2 X.metric μ hμ O K hO hK hOK hT.le
    (source X h) (flow_source_continuousOn_closed X o h U P ρ hloc hT)
  refine ⟨hf, hc, ?_, ?_⟩
  · exact (Yau.LeafProofs.L16HilbertTimeRegularization.continuousOn_memLp_two hc.continuousOn).mono_measure
      (Measure.restrict_mono_set volume Ioo_subset_Icc_self)
  · intro t
    filter_upwards [(hf t).coeFn_toLp] with x hx
    rw [hx]
    exact source_nonneg o h U P ρ hloc x _ (timeClamp_mem T hT.le t).1

end Yau.F04Proof
