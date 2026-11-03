import Yau.Proofs.P06HodgeRegularityStrongModel
import Yau.Proofs.P06HodgeRegularityFormGluing
import Yau.Proofs.P06HodgeRegularityBuffers

/-! Actual local forms reconstructed from the all-degree strong path.
All cutoffs and neighborhoods are internal, before choosing a time slice. -/
noncomputable section
open MeasureTheory Filter Module
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem hodgeStrongPath_exists_local_forms
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (h : ℝ → L2FormHilbert g μ k)
    (hheat : ∀ t, 0 < t → ∃ w, HasDerivAt h w t ∧
      (h t,(-2 : ℝ) • w) ∈ (hodgeCoreOperator g μ hμ k).closure.graph)
    (A : ℝ → RealForm M k) (hA : ∀ t, 0 < t → L2RealForm g.form μ (A t))
    (hAt : ∀ t (ht : 0 < t), realizeActualForm g μ (A t) (hA t ht) = h t) (x : M.Carrier) :
    ∃ (N : Set M.Carrier) (B : ℝ → RealForm M k), IsOpen N ∧ x ∈ N ∧
      (∀ t, 0 < t → SmoothRealForm (B t)) ∧
      (∀ t, 0 < t → ∀ᵐ y ∂μ.restrict N, B t y = A t y) ∧
      ∀ b (I : Fin k → RIdx n) z, z ∈ chartTarget b → ∀ t, 0 < t →
        chartInv b z ∈ N → ContDiffAt ℝ ∞
          (fun p : ComplexVector n × ℝ => formComponents (B p.2) b p.1 I) (z,t) := by
  classical
  have hChart : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have hself : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  obtain ⟨V,hV,hzV,hVO,hcV⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := chartPt x x)) hChart (Set.singleton_subset_iff.mpr hself)
  obtain ⟨χ,hχ,hcχ,hχO,_,hχone⟩ := exists_model_chart_cutoff hChart hcV hVO
  have hone (z : ComplexVector n) (hz : z ∈ V) : χ z = 1 := (hχone z (subset_closure hz)).1
  let N : Set M.Carrier := (extChartAt (ComplexModel n) x).source ∩ (chartPt x ⁻¹' V)
  have hN : IsOpen N := isOpen_extChartAt_preimage' (I := ComplexModel n) x hV
  have hxN : x ∈ N := ⟨mem_extChartAt_source x,hzV (Set.mem_singleton _)⟩
  let b := Module.finBasis ℝ (HodgeJets.Fiber n k)
  let P := hodgeStrongChartModel g μ hμ h x b χ hχ hcχ hχO
  let B (t : ℝ) := chartFormPushforward x (P t)
  have hP := hodgeStrongChartModel_joint_contDiffOn g μ hμ h hheat x b χ hχ hcχ hχO
  have hPt (t : ℝ) (ht : 0 < t) : ContDiff ℝ ∞ (P t) := by
    have hh := hP.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun z (_ : z ∈ (Set.univ : Set (ComplexVector n))) => (show (z,t) ∈ Set.univ ×ˢ Set.Ioi 0 from ⟨Set.mem_univ _,ht⟩))
    exact contDiffOn_univ.mp hh
  have hPK (t : ℝ) : tsupport (P t) ⊆ tsupport χ := hodgeStrongChartModel_tsupport g μ hμ h x b χ hχ hcχ hχO t
  have hcP (t : ℝ) : HasCompactSupport (P t) := hcχ.of_isClosed_subset (isClosed_tsupport _) (hPK t)
  refine ⟨N,B,hN,hxN,?_,?_,?_⟩
  · intro t ht
    exact chartFormPushforward_smooth x (P t) (hPt t ht) (hcP t) ((hPK t).trans hχO)
  · intro t ht
    have hmodel := hodgeStrongChartModel_ae g μ hμ h hheat x b χ hχ hcχ hχO ht (A t) (hA t ht) (hAt t ht)
    have hsource := (realChartPtExtension_quasiMeasurePreserving g.form μ hμ x).ae
      (ae_restrict_of_ae (s := chartTarget x) hmodel)
    have hlocal := ae_restrict_of_ae_restrict_of_subset (show N ⊆ (extChartAt (ComplexModel n) x).source from Set.inter_subset_left) hsource
    filter_upwards [hlocal,ae_restrict_mem hN.measurableSet] with y hy hyN
    have heq : P t (chartPt x y) = chartForm (A t) x (chartPt x y) := by
      simpa only [realChartPtExtension,if_pos hyN.1,hone _ hyN.2,one_smul] using hy
    apply regularityChartForm_fiber_eq x y hyN.1
    have hrec : chartForm (B t) x (chartPt x y) = P t (chartPt x y) :=
      chartFormPushforward_to_chart x (P t) ((extChartAt (ComplexModel n) x).map_source hyN.1)
    rw [hrec,heq]
  · intro b I z hz t ht hyN
    exact regularityChartPushforward_joint_contDiffAt x b P hP hz ht hyN.1 I

end Yau.NodeProofs.P06Aux
