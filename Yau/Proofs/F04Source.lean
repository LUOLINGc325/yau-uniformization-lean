import Yau.Proofs.F04
import Yau.LeafProofs.L14
import Yau.LeafProofs.L22Locality

/-!
The source equation for the actual localized flow. The determinant ratio
is first expressed in one fixed chart before taking spatial derivatives.
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter MeasureTheory

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem metricFamilySmooth_slice {M : ComplexManifold n}
    (h : ℝ → HermitianField M) (I : Set ℝ) (hh : MetricFamilySmooth h I)
    (t : ℝ) (ht : t ∈ I) : MetricSmooth (h t) := by
  intro c a b
  exact (hh c a b).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun z hz => ⟨hz, ht⟩)

theorem hMat_contDiffOn_of_metricSmooth {M : ComplexManifold n}
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun z => hMat h c z i j) (chartTarget c) := by
  have hr : ContDiffOn ℝ ∞ (fun z => (hMat h c z i j).re) (chartTarget c) := by
    convert (hh c (i, 0) (j, 0)).div_const 2 using 1
    funext z
    simp [LeafProofs.L18Aux.realMetricFn_entries]
  have hi : ContDiffOn ℝ ∞ (fun z => (hMat h c z i j).im) (chartTarget c) := by
    convert (hh c (i, 1) (j, 0)).div_const 2 using 1
    funext z
    simp [LeafProofs.L18Aux.realMetricFn_entries]
  have hr' := Complex.ofRealCLM.contDiff.comp_contDiffOn hr
  have hi' := Complex.ofRealCLM.contDiff.comp_contDiffOn hi
  convert hr'.add (hi'.mul (contDiffOn_const (c := Complex.I))) using 1
  funext z
  exact (Complex.re_add_im _).symm

theorem logDet_contDiffOn_of_metricSmooth {M : ComplexManifold n}
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (logDet h c) (chartTarget c) := by
  have hd : ContDiffOn ℝ ∞ (fun z => (hMat h c z).det.re) (chartTarget c) :=
    Complex.reCLM.contDiff.comp_contDiffOn
      (LeafProofs.L18Aux.contDiffOn_matrix_det (hMat_contDiffOn_of_metricSmooth h hh c))
  exact hd.log (fun z hz => (LeafProofs.L18Aux.hMat_det_re_pos h c hz).ne')

theorem rho_in_fixed_chart (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (c : Pt X) (t : ℝ) (ht : 0 ≤ t)
    (z : ComplexVector n) (hz : z ∈ chartTarget c) :
    ρ (chartInv c z) t = logDet X.metric.form c z - logDet (h t) c z := by
  rw [(hloc.2.2.2.2.2.2.2.2.2.1 (chartInv c z) t ht).1,
    hloc.2.2.2.2.2.2.2.2.1 (chartInv c z) t ht]
  change -Real.log (LeafProofs.metricDensityRatio (h t) X.metric.form (chartInv c z)) = _
  rw [LeafProofs.metricDensityRatio_inChart _ _ _ _ hz,
    Real.log_div (LeafProofs.L18Aux.hMat_det_re_pos (h t) c hz).ne'
      (LeafProofs.L18Aux.hMat_det_re_pos X.metric.form c hz).ne']
  dsimp [logDet]
  ring

theorem secondFDeriv_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y - g y)) z v w =
      fderiv ℝ (fderiv ℝ f) z v w - fderiv ℝ (fderiv ℝ g) z v w := by
  have hh := congrArg (fun A => A ![v, w]) (iteratedFDeriv_sub_apply hf hg)
  simpa only [Pi.sub_def, iteratedFDeriv_two_apply, sub_apply,
    Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using hh

theorem leviC_sub {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    leviC (fun y => f y - g y) z = leviC f z - leviC g z := by
  ext i j
  apply Complex.ext
  · simp only [leviC, (LeafProofs.L18Aux.leviMatrix_entry_re_im (hf.sub hg) stdVec i j).1,
      Matrix.sub_apply, Complex.sub_re,
      (LeafProofs.L18Aux.leviMatrix_entry_re_im hf stdVec i j).1,
      (LeafProofs.L18Aux.leviMatrix_entry_re_im hg stdVec i j).1,
      secondFDeriv_sub hf hg]
    ring
  · simp only [leviC, (LeafProofs.L18Aux.leviMatrix_entry_re_im (hf.sub hg) stdVec i j).2,
      Matrix.sub_apply, Complex.sub_im,
      (LeafProofs.L18Aux.leviMatrix_entry_re_im hf stdVec i j).2,
      (LeafProofs.L18Aux.leviMatrix_entry_re_im hg stdVec i j).2,
      secondFDeriv_sub hf hg]
    ring

theorem ricci_flow_identity (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t) :
    ricci (h t) x = ricci X.metric.form x + levi (fun y => ρ y t) x := by
  have hz : chartPt x x ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (mem_extChartAt_source x)
  have heq : (inChart x (fun y => ρ y t)) =ᶠ[𝓝 (chartPt x x)]
      (fun z => logDet X.metric.form x z - logDet (h t) x z) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with z hz'
    exact rho_in_fixed_chart o h U P ρ hloc x t ht z hz'
  have hg := (LeafProofs.L12Aux.logDet_contDiffOn X.metric x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)
  have hh := (logDet_contDiffOn_of_metricSmooth (h t)
    (metricFamilySmooth_slice h (Set.Ici 0) hloc.1.2.1 t ht) x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)
  rw [levi, LeafProofs.L22Aux.leviC_congr_of_eventuallyEq heq,
    leviC_sub (hg.of_le (by norm_num)) (hh.of_le (by norm_num))]
  simp only [ricci]
  abel

theorem rho_source_equation (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (S : ℝ) (hS : 0 < S)
    (x : Pt X) (t : ℝ) (ht : t ∈ Set.Icc 0 S) :
    heatOp h (Set.Icc 0 S) ρ x t = source X h x t := by
  rw [heatOp, rho_derivWithin_Icc o h U P ρ hloc S hS x t ht,
    scalarCurvature, ricci_flow_identity o h U P ρ hloc x t ht.1]
  simp only [laplacian, source, traceWith, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  ring

theorem volume_density_transport (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (t : ℝ) (ht : 0 ≤ t)
    (μg μt : Measure (Pt X)) (hμg : IsRiemannianVolume X.metric.form μg)
    (hμt : IsRiemannianVolume (h t) μt) :
    μt = μg.withDensity (fun x => ENNReal.ofReal (density ρ x t)) := by
  rw [LeafProofs.riemannianVolume_withDensity (h t) X.metric.form μt μg hμt hμg
    (metricFamilySmooth_slice h (Set.Ici 0) hloc.1.2.1 t ht)
    (LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric)]
  congr 1
  funext x
  exact congrArg ENNReal.ofReal (density_eq_det_ratio o h U P ρ hloc x t ht).symm

end Yau.F04Proof
