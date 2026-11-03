import Yau.Proofs.F04VariationalChartTest
import Yau.Proofs.F04EnergyChartWeakGradient
import Yau.Proofs.F04SupportedChartJoint
import Yau.Proofs.F04ChartCompletedForm
import Yau.Proofs.F04ChartPivotPairing
import Yau.Proofs.F04LocalFormMarkov
import Yau.Proofs.F04WeakEquationFromChartTests

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint Yau.Parabolic Yau.ParabolicCandidates Yau.Proofs.F03Aux
  Yau.MassTargetStatements Yau.LeafProofs.L19Aux Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω : Set M.Carrier) :
    CompleteSpace (DirichletEnergy g μ hμ Ω) := dirichletEnergy_completeSpace g μ hμ Ω

/-- The original actual variational solution has genuine chart values,
 completed weak gradients, a product-L2 source, literal local energy and
 the literal weak nondivergence PDE for the supplied evolving metric.
 Every representative, moving test and chart form identity is constructed
 from the original V/J/B solution; no weak PDE or regularity is an inlet. -/
theorem variationalSolution_chart_weakEquation
    (g : SmoothMetric M) (hg : IsKahler g) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (Ω K : Set M.Carrier)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hΩK : Ω ⊆ K)
    (h : ℝ → HermitianField M) {S C α shift : ℝ} (hS : 0 < S)
    (hh : MetricFamilySmooth h (Icc 0 S))
    (B : ℝ → DirichletEnergy g μ hμ Ω →L[ℝ] EnergyDual (DirichletEnergy g μ hμ Ω))
    (hForm : IntrinsicFormBinding g.form μ Ω h S C α shift
      (dirichletL2 g μ hμ Ω) (energyRepresentative g μ hμ Ω) B)
    (f : ℝ → FixedPivot μ Ω) (hf : MemLp f 2 (volume.restrict (Ioo 0 S)))
    (U : ℝ → DirichletEnergy g μ hμ Ω) (R : ℝ → EnergyDual (DirichletEnergy g μ hμ Ω))
    (a : ℝ → FixedPivot μ Ω)
    (hSol : VariationalSolution μ Ω S (dirichletL2 g μ hμ Ω) B f U R a)
    (c : M.Carrier) {O : Set (Space n)} (hO : IsOpen O) (hOC : IsCompact (closure O))
    (hOt : closure O ⊆ chartTarget c) (hMap : chartInv c '' O ⊆ Ω) :
    ∃ (u : Point n → ℝ) (G : Point n → RIdx n → ℝ) (F : Point n → ℝ),
      StronglyMeasurable u ∧ (∀ i, StronglyMeasurable (fun p => G p i)) ∧ StronglyMeasurable F ∧
      MemLp u 2 (productVolume O (Ioo 0 S)) ∧
      (∀ i, MemLp (fun p => G p i) 2 (productVolume O (Ioo 0 S))) ∧
      MemLp F 2 (productVolume O (Ioo 0 S)) ∧
      LocalEnergy O (Ioo 0 S) u G ∧
      WeakEquation O (Ioo 0 S) (flowChartPrincipal h c) (fun _ _ => 0) F u G ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 S),
        ((fun z => u (z, t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (scalarEnergyL2 g μ hμ (U t).val)) ∧
        (∀ i, (fun z => G (z, t) i) =ᵐ[volume.restrict O]
          scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt i (U t).val) ∧
        ((fun z => F (z, t)) =ᵐ[volume.restrict O]
          scalarEnergy_chartRestrictionCLM g μ hμ c hO hOC hOt (l2ZeroExtension μ Ω hΩ.measurableSet (f t))) := by
  obtain ⟨u, G, huM, hGM, hu, hG, hSlices⟩ :=
    dirichletEnergy_chart_joint_representatives g μ hμ Ω U hSol.1 c hO hOC hOt
  obtain ⟨F, hFM, hF, hFSlices⟩ :=
    supportedL2_chart_joint_representative g μ hμ Ω hΩ.measurableSet f hf c hO hOC hOt
  refine ⟨u, G, F, huM, hGM, hFM, hu, hG, hF, ?_, ?_, ?_⟩
  · refine ⟨dirichletEnergy_chart_jointWeakGradient g μ hμ Ω U c hO hOC hOt hu hG hSlices, ?_⟩
    intro V l r _hV _hVC hVO hI
    have hm : productVolume V (Ioo l r) ≤ productVolume O (Ioo 0 S) :=
      Measure.prod_mono (Measure.restrict_mono (subset_closure.trans hVO) le_rfl)
        (Measure.restrict_mono (Ioo_subset_Icc_self.trans hI) le_rfl)
    exact ⟨hu.mono_measure hm, fun i => (hG i).mono_measure hm⟩
  · have hCoeff := flowChartPrincipal_smooth h hh c
    have ha : ∀ i j, ContDiffOn ℝ 1 (fun p => flowChartPrincipal h c p i j) (O ×ˢ Ioo 0 S) := by
      intro i j
      exact (((matrixEntryCLM i j).contDiff.comp_contDiffOn hCoeff.1).mono
        (prod_mono (subset_closure.trans hOt) Ioo_subset_Icc_self)).of_le (by simp)
    apply weakEquation_of_chart_test_integrals hO isOpen_Ioo ha hu hG hF
    intro φ hφ
    let j := dirichletL2 g μ hμ Ω
    have hθ := scalarChart_densityInverseTest g c (subset_closure.trans hOt) hφ
    let Φ := fun t => dirichletCoreToEnergy g μ hμ Ω
      (chartSupportedTestCore g μ hμ Ω c (subset_closure.trans hOt) hMap hθ t)
    let Ψ := fun t => dirichletCoreToEnergy g μ hμ Ω
      (chartSupportedTestCore g μ hμ Ω c (subset_closure.trans hOt) hMap (test_timeDerivative hθ) t)
    have hMove := variationalSolution_chart_test g hg μ hμ Ω K hΩ.measurableSet hK hΩK c
      (subset_closure.trans hOt) hMap hS B f U R a hSol hθ
    change (∫ t in Ioo 0 S, inner ℝ (a t) (j (Ψ t)) - B t (U t) (Φ t) + inner ℝ (f t) (j (Φ t))) = 0 at hMove
    let L := fun p : Point n => deriv (fun t => φ (p.1, t)) p.2
    let H := fun p : Point n => ∑ i, ∑ q, G p q *
      chartWeakTestEntry (fun z => flowChartPrincipal h c (z, p.2)) (fun z => φ (z, p.2)) i q p.1
    let P := fun p : Point n => u p * L p - H p + F p * φ p
    have hφL : MemLp φ 2 (productVolume O (Ioo 0 S)) := by
      rw [productVolume_eq_restrict]
      exact (hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1).restrict _
    have hφt := test_timeDerivative hφ
    have hLL : MemLp L 2 (productVolume O (Ioo 0 S)) := by
      rw [productVolume_eq_restrict]
      exact (hφt.1.continuous.memLp_of_hasCompactSupport hφt.2.1).restrict _
    have hUT := hu.integrable_mul hLL
    have hHT : Integrable H (productVolume O (Ioo 0 S)) :=
      integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ (fun q _ =>
        (hG q).integrable_mul (chartWeakTestEntry_spacetime_memLp hO isOpen_Ioo ha hφ i q)))
    have hFT := hF.integrable_mul hφL
    have hPT : Integrable P (productVolume O (Ioo 0 S)) := by
      have he : P = (u * L - H) + F * φ := by funext p; rfl
      rw [he]
      exact (hUT.sub hHT).add hFT
    change Integrable P ((volume.restrict O).prod (volume.restrict (Ioo 0 S))) at hPT
    change (∫ p, P p ∂(volume.restrict O).prod (volume.restrict (Ioo 0 S))) = 0
    rw [integral_prod_symm _ hPT]
    apply (integral_congr_ae ?_).trans hMove
    filter_upwards [hSlices, hFSlices, hSol.2.2.2.2.1, ae_restrict_mem measurableSet_Ioo,
      hUT.prod_left_ae, hHT.prod_left_ae, hFT.prod_left_ae] with t ht hFt hat htI hUIt hHIt hFIt
    have hAT : inner ℝ (a t) (j (Ψ t)) = ∫ z in O, u (z, t) * L (z, t) := by
      have hD : Ψ t = dirichletCoreToEnergy g μ hμ Ω
          (chartSupportedTestCore g μ hμ Ω c (subset_closure.trans hOt) hMap
            (scalarChart_densityInverseTest g c (subset_closure.trans hOt) (test_timeDerivative hφ)) t) := by
        dsimp only [Ψ]
        rw [chartSupportedTestCore_density_timeDerivative g μ hμ Ω c (subset_closure.trans hOt) hMap hφ t]
      rw [hD]
      have he := supportedL2_chartDensityTest_inner g μ hμ Ω hΩ.measurableSet c hO hOC hOt hMap
        (test_timeDerivative hφ) t (a t)
      change inner ℝ (a t) (j _) = _ at he
      rw [he]
      have hZ : l2ZeroExtension μ Ω hΩ.measurableSet (a t) = scalarEnergyL2 g μ hμ (U t).val := by
        rw [hat, dirichletL2_zeroExtension]
      rw [hZ]
      apply integral_congr_ae
      filter_upwards [ht.1] with z hz
      exact congrArg (fun q : ℝ => q * L (z, t)) hz.symm
    have hBT : B t (U t) (Φ t) = ∫ z in O, H (z, t) := by
      have he := localCoreForm_chart_gradient_integral g μ hμ Ω h t
        (metricFamilySmooth_slice h (Icc 0 S) hh t (Ioo_subset_Icc_self htI)) (B t)
        (intrinsicForm_core_formula g hg μ hμ Ω hΩ h S C α shift B hForm t (Ioo_subset_Icc_self htI))
        c hO hOC hOt hMap hφ (U t)
      change B t (U t) (Φ t) = _ at he
      rw [he]
      apply integral_congr_ae
      have hd : ∀ᵐ z ∂volume.restrict O, ∀ q : RIdx n,
          scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt q (U t).val z = G (z, t) q :=
        ae_all_iff.mpr (fun q => (ht.2 q).symm)
      filter_upwards [hd] with z hz
      change (∑ i, ∑ q, scalarEnergy_chartDerivativeCLM g μ hμ c hO hOC hOt q (U t).val z *
        chartWeakTestEntry (fun w => flowChartPrincipal h c (w, t)) (fun w => φ (w, t)) i q z) = _
      simp_rw [hz]
      rfl
    have hST : inner ℝ (f t) (j (Φ t)) = ∫ z in O, F (z, t) * φ (z, t) := by
      have he := supportedL2_chartDensityTest_inner g μ hμ Ω hΩ.measurableSet c hO hOC hOt hMap hφ t (f t)
      change inner ℝ (f t) (j (Φ t)) = _ at he
      rw [he]
      apply integral_congr_ae
      filter_upwards [hFt] with z hz
      exact congrArg (fun q : ℝ => q * φ (z, t)) hz.symm
    change Integrable (fun z => u (z, t) * L (z, t)) (volume.restrict O) at hUIt
    change Integrable (fun z => F (z, t) * φ (z, t)) (volume.restrict O) at hFIt
    change (∫ z in O, u (z, t) * L (z, t) - H (z, t) + F (z, t) * φ (z, t)) = _
    have hAdd := integral_add (hUIt.sub hHIt) hFIt
    simp only [Pi.sub_apply] at hAdd
    rw [hAdd, integral_sub hUIt hHIt, ← hAT, ← hBT, ← hST]
  · filter_upwards [hSlices, hFSlices] with t ht hFt
    exact ⟨ht.1, ht.2, hFt⟩

end Yau.F04Proof
