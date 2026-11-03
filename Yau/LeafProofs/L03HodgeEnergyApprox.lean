import Yau.LeafProofs.L03HodgeLocalRegularization
import Yau.LeafProofs.L03ModelFirstJetLimits
import Yau.LeafProofs.L03ChartStrongLimits
import Yau.LeafProofs.L03HodgeIMS

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

/-- The actual lower Hodge derivative, with its genuine zero-degree convention. -/
def hodgeLowerRealForm (g : HermitianField M) : (j : ℕ) → RealForm M j → RealForm M (j - 1)
  | 0, _ => 0
  | j + 1, A => codifferentialRealForm g A

def modelHodgeLowerJet (g : HermitianField M) (x : M.Carrier) (z : ComplexVector n) :
    (j : ℕ) → ((HodgeJets.Fiber n j) × (ComplexVector n →L[ℝ] HodgeJets.Fiber n j)) →L[ℝ]
      HodgeJets.Fiber n (j - 1)
  | 0 => 0
  | j + 1 => modelCodifferentialJetCLM (k := j) g x z

theorem modelHodgeLowerJet_contDiffOn (g : SmoothMetric M) (x : M.Carrier)
    (p : (HodgeJets.Fiber n k) × (ComplexVector n →L[ℝ] HodgeJets.Fiber n k)) :
    ContDiffOn ℝ ∞ (fun z => modelHodgeLowerJet g.form x z k p) (chartTarget x) := by
  cases k with
  | zero => exact contDiffOn_const
  | succ j => exact modelCodifferentialJetCLM_contDiffOn g x p.1 p.2

theorem chart_hodgeLowerRealForm (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : SmoothRealForm A)
    (x : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    chartForm (hodgeLowerRealForm g.form k A) x z =
      modelHodgeLowerJet g.form x z k (chartForm A x z, fderiv ℝ (chartForm A x) z) := by
  cases k with
  | zero => ext v; rfl
  | succ j => exact HodgeJets.chart_codifferential g μ hμ A hA x hz

theorem hodgeLowerRealForm_zero_outside_chart (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M k) (hA : SmoothRealForm A)
    (x : M.Carrier) (hAs : closure {y | A y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source)
    (y : M.Carrier) (hy : y ∉ (extChartAt (ComplexModel n) x).source) :
    hodgeLowerRealForm g.form k A y = 0 := by
  cases k with
  | zero => rfl
  | succ j =>
      by_contra hn
      exact hy (hAs ((codifferentialRealForm_support_subset g μ hμ A hA) (subset_closure hn)))

/-- Genuine compact smooth approximations of a chart multiplier of an
original rough Hodge deficiency field converge in the actual d/δ graph.
The raw derivative outputs are constructed from ordinary L² limits. -/
theorem exists_chart_hodge_energy_approximation {α : Type*} [Fintype α] [DecidableEq α]
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (hmax : OperatorCandidates.HodgeMaximalGraph g.form μ A (-A))
    (x : M.Carrier) (b : Basis α ℝ (HodgeJets.Fiber n k))
    (χ : ComplexVector n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ chartTarget x) :
    ∃ L : Set M.Carrier, IsCompact L ∧
      ∃ (As : ℕ → RealForm M k) (V : RealForm M (k + 1)) (W : RealForm M (k - 1)),
      (∀ m, SmoothRealForm (As m) ∧ CompactlySupportedRealForm (As m) ∧
        closure {y | As m y ≠ 0} ⊆ L) ∧ L2RealForm g.form μ V ∧ L2RealForm g.form μ W ∧
      Tendsto (fun m => formL2DistanceSq g.form μ (As m)
        (multiplyRealForm (L18Aux.chartPushforwardZero x χ) A)) atTop (𝓝 0) ∧
      Tendsto (fun m => formL2DistanceSq g.form μ (exteriorRealForm (As m)) V) atTop (𝓝 0) ∧
      Tendsto (fun m => formL2DistanceSq g.form μ (hodgeLowerRealForm g.form k (As m)) W) atTop (𝓝 0) := by
  classical
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by rw [lebesgueC_eq_volume]; infer_instance
  obtain ⟨K0, hK0, hK0O, U, D, hU, hUK0, hUt, hD, hDK0, hDt⟩ :=
    HodgeDivergenceWeak.exists_localized_smooth_gradient_limits g μ hμ A hmax x b χ hχ hcχ hχO
  let K := K0 ∪ tsupport χ
  have hK : IsCompact K := hK0.union hcχ
  have hKO : K ⊆ chartTarget x := Set.union_subset hK0O hχO
  have hUK (m : ℕ) (c : α) : tsupport (fun z => U m z c) ⊆ K := (hUK0 m c).trans Set.subset_union_left
  have hDK (q : RIdx n × α) : tsupport (fun z => D z q) ⊆ K := (hDK0 q).trans Set.subset_union_left
  let u := HodgeDivergenceWeak.localizedInput x b χ A
  have hu := (HodgeDivergenceWeak.localized_data_memLp g μ hμ A hmax.1 x b χ hχ hcχ hχO).1
  have huK (c : α) : tsupport (fun z => u z c) ⊆ K :=
    ((HodgeDivergenceWeak.localized_data_support g.form x b χ A).1 c).trans Set.subset_union_right
  let G := fun m => basisField b (U m)
  let G0 := basisField b u
  have hG (m : ℕ) : ContDiff ℝ ∞ (G m) := basisField_contDiff b (U m) (hU m)
  have hGK (m : ℕ) : tsupport (G m) ⊆ K := basisField_tsupport_subset b (U m) hK.isClosed (hUK m)
  have hG0K : tsupport G0 ⊆ K := basisField_tsupport_subset b u hK.isClosed huK
  have hG0m : MemLp G0 2 (lebesgueC n) := memLp_finsetSum (f := fun c z => u z c • b c) Finset.univ
    (fun c _ => (ContinuousLinearMap.toSpanSingleton ℝ (b c)).comp_memLp' (hu c))
  have hUm (m : ℕ) (c : α) : MemLp (fun z => U m z c) 2 (lebesgueC n) :=
    (hU m c).continuous.memLp_of_hasCompactSupport (hK.of_isClosed_subset (isClosed_tsupport _) (hUK m c))
  have hGlim := integral_sq_tendsto_zero_of_basis_coordinates (lebesgueC n) b (fun m z => G m z - G0 z)
    (fun m c => ((hUm m c).sub (hu c)).ae_eq (Filter.Eventually.of_forall fun z => by
      simp only [Pi.sub_apply, G, G0, map_sub, Finsupp.sub_apply, basisField_coordinates, u]))
    (fun c => by simpa only [G, G0, map_sub, Finsupp.sub_apply, basisField_coordinates, u] using hUt c)
  have hG0 : G0 = (fun z => χ z • chartForm A x z) := by
    funext z
    apply b.repr.injective
    ext c
    simp only [G0, basisField_coordinates, map_smul, Finsupp.smul_apply, smul_eq_mul,
      u, HodgeDivergenceWeak.localizedInput]
  have hinput : chartFormPushforward x G0 = multiplyRealForm (L18Aux.chartPushforwardZero x χ) A := by
    rw [hG0]
    exact chartFormPushforward_scalar_chartForm x χ A
  obtain ⟨Pd, V0, hPd, hPdK, hV0, hV0K, hPdjet, hPdlim⟩ := exists_model_firstJet_output_limit (lebesgueC n)
    b (Module.finBasis ℝ (HodgeJets.Fiber n (k + 1))) (fun _ => modelExteriorJetCLM n k)
    (chartTarget x) (isOpen_extChartAt_target (I := ComplexModel n) x) (fun _ => contDiffOn_const)
    hK hKO U u D hU hUK hu huK hD hDK hUt (fun i c => hDt (i, c))
  obtain ⟨Pl, W0, hPl, hPlK, hW0, hW0K, hPljet, hPllim⟩ := exists_model_firstJet_output_limit (lebesgueC n)
    b (Module.finBasis ℝ (HodgeJets.Fiber n (k - 1))) (fun z => modelHodgeLowerJet g.form x z k)
    (chartTarget x) (isOpen_extChartAt_target (I := ComplexModel n) x)
    (modelHodgeLowerJet_contDiffOn g x) hK hKO U u D hU hUK hu huK hD hDK hUt (fun i c => hDt (i, c))
  let As := fun m => chartFormPushforward x (G m)
  have hcG (m : ℕ) : HasCompactSupport (G m) := hK.of_isClosed_subset (isClosed_tsupport _) (hGK m)
  have hAs (m : ℕ) : SmoothRealForm (As m) ∧ CompactlySupportedRealForm (As m) :=
    ⟨chartFormPushforward_smooth x (G m) (hG m) (hcG m) ((hGK m).trans hKO),
      chartFormPushforward_compactlySupported x (G m) (hG m) (hcG m) ((hGK m).trans hKO)⟩
  have hAsO (m : ℕ) : closure {y | As m y ≠ 0} ⊆ (extChartAt (ComplexModel n) x).source :=
    chartFormPushforward_source_support x (G m) (hG m) (hcG m) ((hGK m).trans hKO)
  have hchart (m : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget x) : chartForm (As m) x =ᶠ[𝓝 z] G m := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with y hy
    exact chartFormPushforward_to_chart x (G m) hy
  have hdeq (m : ℕ) : chartFormPushforward x (Pd m) = exteriorRealForm (As m) := by
    apply chartFormPushforward_eq_of_chart_and_zero_off
    · intro z hz
      rw [HodgeJets.chart_exterior (As m) (hAs m).1 x hz,
        (hchart m hz).eq_of_nhds, (hchart m hz).fderiv_eq]
      exact (hPdjet m z).symm
    · intro y hy
      by_contra hn
      exact hy (hAsO m ((representsExterior_support_subset (exteriorRealForm_represents (As m) (hAs m).1)) (subset_closure hn)))
  have hleq (m : ℕ) : chartFormPushforward x (Pl m) = hodgeLowerRealForm g.form k (As m) := by
    apply chartFormPushforward_eq_of_chart_and_zero_off
    · intro z hz
      rw [chart_hodgeLowerRealForm g μ hμ (As m) (hAs m).1 x hz,
        (hchart m hz).eq_of_nhds, (hchart m hz).fderiv_eq]
      exact (hPljet m z).symm
    · exact hodgeLowerRealForm_zero_outside_chart g μ hμ (As m) (hAs m).1 x (hAsO m)
  have hVraw := chartFormPushforward_raw_properties g μ hμ x V0 hV0
    (hK.of_isClosed_subset (isClosed_tsupport _) hV0K) (hV0K.trans hKO)
  have hWraw := chartFormPushforward_raw_properties g μ hμ x W0 hW0
    (hK.of_isClosed_subset (isClosed_tsupport _) hW0K) (hW0K.trans hKO)
  let L := chartInv x '' K
  have hL : IsCompact L := hK.image_of_continuousOn ((continuousOn_extChartAt_symm (I := ComplexModel n) x).mono hKO)
  refine ⟨L, hL, As, chartFormPushforward x V0, chartFormPushforward x W0, ?_, hVraw.1, hWraw.1, ?_, ?_, ?_⟩
  · intro m
    exact ⟨(hAs m).1, (hAs m).2,
      (chartFormPushforward_image_support x (G m) (hcG m) ((hGK m).trans hKO)).trans (Set.image_mono (hGK m))⟩
  · simpa only [As, hinput] using chartFormPushforward_strong_l2_tendsto g μ hμ x hK hKO G hG hGK G0 hG0m hG0K hGlim.2
  · simpa only [hdeq] using chartFormPushforward_strong_l2_tendsto g μ hμ x hK hKO Pd hPd hPdK V0 hV0 hV0K hPdlim
  · simpa only [hleq] using chartFormPushforward_strong_l2_tendsto g μ hμ x hK hKO Pl hPl hPlK W0 hW0 hW0K hPllim

end Yau.LeafProofs.L03
