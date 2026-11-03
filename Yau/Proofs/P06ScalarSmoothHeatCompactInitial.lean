import Yau.Proofs.P06ScalarSmoothHeatCompactChart

/-! The literal original all-chart, all-order initial class for compact
smooth forms. This is independent of form degree. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.ScalarSmooth
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

section CompactDatum
variable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A)
    (U : ℝ → RealForm M k) (hU : ∀ t, 0 < t → SmoothRealForm (U t))
    (hUL : ∀ t, 0 < t → L2RealForm g.form μ (U t))
    (hUr : ∀ t ht, realizeActualForm g μ (U t) (hUL t ht) =
      hodgeHeatHilbert g μ hμ k t (compactHodgeIterateHilbert g μ hμ A hA hcA 0))
include hA hcA hU hUL hUr

theorem hodgeHeat_compact_initial_cutoff_component
    (x : M.Carrier) (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hχO : tsupport χ ⊆ chartTarget x)
    (j : ℕ) (I : Fin k → RIdx n) (ε : ℝ) (hε : 0 < ε) :
    ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ z,
      ‖iteratedFDeriv ℝ j (fun w => χ w * formComponents (U t-A) x w I) z‖ < ε := by
  classical
  let b := Module.finBasis ℝ (HodgeJets.Fiber n k)
  let F := fun c t z => χ z * hodgeRegularityCoord b (U t-A) x z c
  let a := fun c => b c (fun r => realVec (I r))
  have hsF (c) (t : ℝ) (ht : 0 < t) : ContDiff ℝ ∞ (F c t) := by
    have hsD : SmoothRealForm (U t-A) := fun y J => (hU t ht y J).sub (hA y J)
    exact (scalar_cutoff_contDiff_properties
      (isOpen_extChartAt_target (I := ComplexModel n) x) χ hχ hcχ hχO _
      (hodgeRegularityCoord_contDiffOn b (U t-A) hsD x c)).1
  have hsmall (c) : ∀ δ : ℝ, 0 < δ → ∃ τ > 0, ∀ t, 0 < t → t < τ →
      ∀ z, ‖iteratedFDeriv ℝ j (F c t) z‖ < δ :=
    hodgeHeat_compact_initial_chart_coord g μ hμ A hA hcA U hU hUL hUr
      x b χ hχ hcχ hχO c j
  obtain ⟨τ,hτ,hh⟩ := iteratedFDeriv_uniform_small_sum F a hsF j hsmall ε hε
  have he (t : ℝ) : (fun z => ∑ c, a c * F c t z) =
      fun z => χ z * formComponents (U t-A) x z I := by
    funext z
    have hb := congrArg (fun P : HodgeJets.Fiber n k => P (fun r => realVec (I r)))
      (b.sum_repr (chartForm (U t-A) x z))
    have hb' : (∑ c, hodgeRegularityCoord b (U t-A) x z c * a c) =
        formComponents (U t-A) x z I := by
      simpa only [ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,
        smul_eq_mul,hodgeRegularityCoord,a,chartForm_apply_basis] using hb
    dsimp only [F]
    calc
      _ = χ z * ∑ c, hodgeRegularityCoord b (U t-A) x z c * a c := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := congrArg (χ z * ·) hb'
  refine ⟨τ,hτ,?_⟩
  intro t ht htτ z
  simpa only [he t] using hh t ht htτ z

/-- Every compact smooth original geometric datum attains all its
spatial jets on every compact subset of every chart, for any actual smooth
representative of its already constructed original Hilbert heat. -/
theorem hodgeHeat_compact_initial (hzero : U 0 = A) : FormSmoothInitial U A := by
  refine ⟨hzero,?_⟩
  intro x K hK hKO j I ε hε
  have hChart := isOpen_extChartAt_target (I := ComplexModel n) x
  obtain ⟨V,hV,hKV,hVO,hcV⟩ := exists_open_between_and_isCompact_closure hK hChart hKO
  obtain ⟨χ,hχ,hcχ,hχO,_,hχone⟩ := exists_model_chart_cutoff hChart hcV hVO
  obtain ⟨τ,hτ,hh⟩ := hodgeHeat_compact_initial_cutoff_component g μ hμ A hA hcA U hU hUL hUr
    x χ hχ hcχ hχO j I ε hε
  refine ⟨τ,hτ,?_⟩
  intro t ht htτ z hz
  have he : (fun w => χ w * formComponents (U t-A) x w I) =ᶠ[𝓝 z]
      (fun w => formComponents (U t) x w I - formComponents A x w I) := by
    filter_upwards [hV.mem_nhds (hKV hz)] with w hw
    rw [(hχone w (subset_closure hw)).1,one_mul]
    rfl
  have hjet := (he.iteratedFDeriv ℝ j).eq_of_nhds
  rw [← hjet]
  exact hh t ht htτ z

end CompactDatum
end Yau.NodeProofs.P06Aux.ScalarSmooth
