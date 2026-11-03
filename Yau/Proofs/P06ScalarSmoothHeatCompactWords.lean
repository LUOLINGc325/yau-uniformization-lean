import Yau.Proofs.P06ScalarSmoothHeatGraphJets
import Yau.Proofs.P06ScalarSmoothHeatCompactGraph

/-! Compact smooth data attain every compact chart word derivative at
time zero. This uses finite graph continuity, not a positive-time smoothing
constant that could diverge as the time approaches zero. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff BoundedContinuousFunction InnerProductSpace

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.LeafProofs Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

theorem finiteChartProjection_actual_ae {α : Type} [Fintype α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (N : ℕ) (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α)
    (f : hodgeGraphChains g μ hμ k N) (A : RealForm M k)
    (hA : L2RealForm g.form μ A) (hAf : realizeActualForm g μ A hA = f.val 0) :
    (fun y => χ ((hodgeRegularityFinEquiv n).symm y) *
      hodgeRegularityCoord b A x ((hodgeRegularityFinEquiv n).symm y) c) =ᵐ[volume]
      (finiteChartProjection g μ hμ N x b χ hχ hcχ hχO c f :
        (Fin (Fintype.card (RIdx n)) → ℝ) → ℝ) := by
  have hPAE := chartProjection_actual_ae g μ hμ x χ hχ hcχ hχO
    (b.coord c).toContinuousLinearMap A hA
  rw [hAf] at hPAE
  have hp := (hodgeRegularityFinEquiv_symm_measurePreserving n).quasiMeasurePreserving.ae hPAE
  have hc := Lp.coeFn_compMeasurePreserving
    (chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap (f.val 0))
    (hodgeRegularityFinEquiv_symm_measurePreserving n)
  filter_upwards [hp,hc] with y hy hcy
  have hy' : (chartProjection g μ hμ x χ hχ hcχ hχO (b.coord c).toContinuousLinearMap
      (f.val 0)) ((hodgeRegularityFinEquiv n).symm y) =
      χ ((hodgeRegularityFinEquiv n).symm y) *
        hodgeRegularityCoord b A x ((hodgeRegularityFinEquiv n).symm y) c := by
    simpa only [chartFunctional,hodgeRegularityCoord,
      LinearMap.coe_toContinuousLinearMap',Basis.coord_apply] using hy
  exact hy'.symm.trans hcy.symm

theorem compactInitialGraphJet_uniform {E : Type*} [TopologicalSpace E]
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) (N : ℕ)
    (L : hodgeGraphChains g μ hμ k N →L[ℝ] (E →ᵇ ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ z,
      |L (compactInitialGraphChain g μ hμ A hA hcA N t) z| < ε := by
  have hlim := compactInitialGraphJet_tendsto_zero g μ hμ A hA hcA N L
  have hnorm : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖L (compactInitialGraphChain g μ hμ A hA hcA N t)‖ < ε := by
    have hnormlim : Tendsto
        (fun t => ‖L (compactInitialGraphChain g μ hμ A hA hcA N t)‖)
        (𝓝[≥] (0 : ℝ)) (𝓝 (0 : ℝ)) := by simpa only [norm_zero] using hlim.norm
    have hn := hnormlim.eventually (Iio_mem_nhds hε)
    exact hn.filter_mono (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  obtain ⟨τ,hτ,hh⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnorm
  refine ⟨τ,hτ,fun t ht htτ z => ?_⟩
  exact (show |L (compactInitialGraphChain g μ hμ A hA hcA N t) z| ≤
      ‖L (compactInitialGraphChain g μ hμ A hA hcA N t)‖ from
    by simpa only [Real.norm_eq_abs] using
      BoundedContinuousFunction.norm_coe_le_norm
        (L (compactInitialGraphChain g μ hμ A hA hcA N t)) z).trans_lt (hh ⟨ht,htτ⟩)

theorem hodgeHeat_compact_initial_chart_word {α : Type} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (U : ℝ → RealForm M k) (hU : ∀ t, 0 < t → SmoothRealForm (U t))
    (hUL : ∀ t, 0 < t → L2RealForm g.form μ (U t))
    (hUr : ∀ t ht, realizeActualForm g μ (U t) (hUL t ht) =
      hodgeHeatHilbert g μ hμ k t (compactHodgeIterateHilbert g μ hμ A hA hcA 0))
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) (c : α)
    (w : List (Fin (Fintype.card (RIdx n)))) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ y,
      |regularityCoefficientWord (fun i => Pi.single i 1) w
        (fun z => χ ((hodgeRegularityFinEquiv n).symm z) *
          hodgeRegularityCoord b (U t - A) x ((hodgeRegularityFinEquiv n).symm z) c) y| < ε := by
  let N := w.length + Fintype.card (RIdx n)
  obtain ⟨L,hLK,hpair⟩ := exists_finiteGraphJetCLM g μ hμ N x b χ hχ hcχ hχO c w le_rfl
  obtain ⟨τ,hτ,hh⟩ := compactInitialGraphJet_uniform g μ hμ A hA hcA N L ε hε
  refine ⟨τ,hτ,?_⟩
  intro t ht htτ y
  have hD : L2RealForm g.form μ (U t - A) := l2RealForm_sub g μ _ _ (hUL t ht)
    (compactHodgeIterate_l2 g μ hμ A hA hcA 0)
  have hDr : realizeActualForm g μ (U t - A) hD =
      (compactInitialGraphChain g μ hμ A hA hcA N t).val 0 := by
    change _ = hodgeHeatHilbert g μ hμ k t (compactHodgeIterateHilbert g μ hμ A hA hcA 0) -
      compactHodgeIterateHilbert g μ hμ A hA hcA 0
    rw [realizeActualForm_sub g μ (U t) A (hUL t ht)
      (compactHodgeIterate_l2 g μ hμ A hA hcA 0),hUr t ht]
    rfl
  have hsD : SmoothRealForm (U t - A) := fun a I => (hU t ht a I).sub (hA a I)
  have hF := scalar_cutoff_contDiff_properties
    (isOpen_extChartAt_target (I := ComplexModel n) x) χ hχ hcχ hχO _
    (hodgeRegularityCoord_contDiffOn b (U t - A) hsD x c)
  have hAE := finiteChartProjection_actual_ae g μ hμ N x b χ hχ hcχ hχO c
    (compactInitialGraphChain g μ hμ A hA hcA N t) (U t-A) hD hDr
  have he := distributionLift_eq_smooth_word volume
    (finiteChartProjection g μ hμ N x b χ hχ hcχ hχO c)
    (fun i => Pi.single i 1) w L (hcχ.image (hodgeRegularityFinEquiv n).continuous) hLK hpair
    (compactInitialGraphChain g μ hμ A hA hcA N t) _
    (hF.1.comp (hodgeRegularityFinEquiv n).symm.contDiff)
    (hF.2.1.comp_homeomorph (hodgeRegularityFinEquiv n).symm.toHomeomorph) hAE y
  simpa only [Function.comp_def,he] using hh t ht htτ y

end Yau.NodeProofs.P06Aux.ScalarSmooth
