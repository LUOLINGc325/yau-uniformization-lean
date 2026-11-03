import Yau.Proofs.F04CompactDifferentialMembership
import Yau.Proofs.F04ClosedSpatialDerivative
import Yau.Proofs.F04CompactLpProfiles
import Yau.Proofs.F04GraphDifferentialLinear

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace ENNReal

noncomputable section

set_option maxHeartbeats 1000000

namespace Yau.F04Proof

open Yau.Blueprint Yau.Proofs.F03Aux Yau.LeafProofs.L03 Yau.LeafProofs.L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The actual spatial differential profile is continuous in the completed
L2 form norm. No H10 condition on the scalar profile or its boundary is used. -/
theorem compact_scalar_differential_profile_L2
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (O K : Set M.Carrier) (hO : MeasurableSet O) (hK : IsCompact K) (hOK : O ⊆ K)
    {S : ℝ} (hS : 0 < S) (v : M.Carrier → ℝ → ℝ) (hv : SmoothSpaceTime v (Icc 0 S)) :
    ∃ hD : ∀ t : ℝ, L2RealForm g.form (μ.restrict O)
      (scalarExterior (fun x => v x (timeClamp S hS.le t))),
      Continuous (fun t => realizeL2Form g (μ.restrict O)
        (L2FormSpace.ofSection (scalarExterior (fun x => v x (timeClamp S hS.le t))) (hD t))) := by
  let := Yau.LeafProofs.L18Aux.riemannianVolume_locallyFinite g μ hμ
  let : IsFiniteMeasure (μ.restrict O) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (lt_of_le_of_lt (measure_mono hOK) hK.measure_lt_top)⟩
  have hslice (t : ℝ) (ht : t ∈ Icc 0 S) : SmoothFn (fun x => v x t) := fun c =>
    (hv c).comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hz => ⟨hz, ht⟩)
  let A := fun t => scalarExterior (fun x => v x (timeClamp S hS.le t))
  have hA (t : ℝ) : L2RealForm g.form (μ.restrict O) (A t) :=
    scalarExterior_L2_on_compact_domain g μ hμ O K hO hK hOK _
      (hslice _ (timeClamp_mem S hS.le t))
  let D := fun t => realizeL2Form g (μ.restrict O) (L2FormSpace.ofSection (A t) (hA t))
  have hDon : ContinuousOn D (Icc 0 S) := by
    intro t ht
    let w := fun x s => v x s - v x t
    have hw : SmoothSpaceTime w (Icc 0 S) := fun c => (hv c).sub
      ((hslice t ht c).comp contDiffOn_fst (fun _ hp => hp.1))
    let H := fun x s => scalarGradientPair g.form (w · s) (w · s) x
    have hH : ContinuousOn (fun p : M.Carrier × ℝ => H p.1 p.2) (univ ×ˢ Icc 0 S) :=
      smoothSpaceTime_gradientPair_continuousOn g.form
        (Yau.LeafProofs.L12Aux.metricSmooth_of_smoothMetric g) hS hw hw
    obtain ⟨C, hCb⟩ := (hK.prod isCompact_Icc).bddAbove_image
      (hH.norm.mono (prod_mono (subset_univ _) (Subset.refl _)))
    let G := fun s x => formNormSq g.form (A s - A t) x
    have hGEq (s : ℝ) (hs : s ∈ Icc 0 S) (x : M.Carrier) : G s x = H x s := by
      dsimp only [G, H, w, A]
      rw [timeClamp_eq_of_mem S hS.le hs, timeClamp_eq_of_mem S hS.le ht,
        ← scalarExterior_sub (hslice s hs) (hslice t ht)]
      have hdiff : SmoothFn ((fun y => v y s) - (fun y => v y t)) :=
        fun c => (hslice s hs c).sub (hslice t ht c)
      change formInner g.form (scalarExterior ((fun y => v y s) - (fun y => v y t)))
        (scalarExterior ((fun y => v y s) - (fun y => v y t))) x =
          scalarGradientPair g.form ((fun y => v y s) - (fun y => v y t))
            ((fun y => v y s) - (fun y => v y t)) x
      exact scalarExterior_inner g.form hdiff hdiff x
    have hGzero (x : M.Carrier) : G t x = 0 := by
      dsimp only [G]
      rw [sub_self, formNormSq_zero]
      rfl
    have hGm (s : ℝ) : AEStronglyMeasurable (G s) (μ.restrict O) :=
      (formNormSq_integrable g (μ.restrict O) (A s - A t)
        ((l2FormSubmodule g (μ.restrict O) 1).sub_mem (hA s) (hA t))).aestronglyMeasurable
    have hGb : ∀ᶠ s in 𝓝[Icc 0 S] t, ∀ᵐ x ∂μ.restrict O, ‖G s x‖ ≤ C := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      filter_upwards [ae_restrict_mem hO] with x hx
      rw [hGEq s hs x]
      exact hCb ⟨(x, s), ⟨hOK hx, hs⟩, rfl⟩
    have hGl : ∀ᵐ x ∂μ.restrict O, Tendsto (fun s => G s x) (𝓝[Icc 0 S] t) (𝓝 (0 : ℝ)) := by
      apply ae_of_all
      intro x
      have hmap : ContinuousOn (fun s : ℝ => (x, s)) (Icc 0 S) :=
        continuousOn_const.prodMk continuousOn_id
      have hmapto : MapsTo (fun s : ℝ => (x, s)) (Icc 0 S) (univ ×ˢ Icc 0 S) :=
        fun _ hs => ⟨mem_univ x, hs⟩
      have hxc : ContinuousOn (fun s => H x s) (Icc 0 S) := by
        simpa only [Function.comp_def] using hH.comp hmap hmapto
      have hz : H x t = 0 := (hGEq t ht x).symm.trans (hGzero x)
      have hl : Tendsto (fun s => H x s) (𝓝[Icc 0 S] t) (𝓝 (0 : ℝ)) := by
        have hc := hxc t ht
        change Tendsto (fun s => H x s) (𝓝[Icc 0 S] t) (𝓝 (H x t)) at hc
        rw [hz] at hc
        exact hc
      have heq : (fun s => G s x) =ᶠ[𝓝[Icc 0 S] t] (fun s => H x s) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact hGEq s hs x
      exact (tendsto_congr' heq).mpr hl
    have hInt := tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      (Eventually.of_forall hGm) hGb (integrable_const C) hGl
    have hnorm (s : ℝ) : ‖D s - D t‖ ^ 2 = ∫ x, G s x ∂μ.restrict O := by
      dsimp only [D]
      rw [← realize_section_sub g (μ.restrict O) (A s) (A t) (hA s) (hA t)
        ((l2FormSubmodule g (μ.restrict O) 1).sub_mem (hA s) (hA t)), realizeL2Form_norm_sq]
      rfl
    have hs : Tendsto (fun s => ‖D s - D t‖ ^ 2) (𝓝[Icc 0 S] t) (𝓝 (0 : ℝ)) := by
      simpa only [hnorm, integral_zero] using hInt
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr
  have hIdem (t : ℝ) : D (timeClamp S hS.le t) = D t := by
    apply (realizeL2Form_eq_iff_ae g (μ.restrict O) _ _).mpr
    apply ae_of_all
    intro x
    change scalarExterior (fun y => v y (timeClamp S hS.le (timeClamp S hS.le t))) x =
      scalarExterior (fun y => v y (timeClamp S hS.le t)) x
    rw [timeClamp_eq_of_mem S hS.le (timeClamp_mem S hS.le t)]
  have hDcont : Continuous D :=
    (hDon.comp_continuous (continuous_timeClamp S hS.le)
      (fun t => timeClamp_mem S hS.le t)).congr hIdem
  exact ⟨hA, hDcont⟩

end Yau.F04Proof
