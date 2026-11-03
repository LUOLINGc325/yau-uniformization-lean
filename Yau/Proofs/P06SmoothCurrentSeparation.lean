import Yau.Proofs.P06SmoothCurrentSeparationTests
import Yau.Proofs.P06TracePairing

/-! Smooth compact positive (1,1) test forms separate the pointwise positive
cone of smooth forms, without any global L² or boundedness assumption. -/
noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux.CurrentSeparation
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03
open Yau.NodeProofs.G04Aux WeakCurrent
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

/-- Positive compact smooth tests detect the original pointwise form order.
The scalar bump separation is applied to the actual metric trace density. -/
theorem smooth_formLE_of_compact_positive_tests
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hsA : SmoothRealForm A) (h11A : RealOneOne A)
    (ht : ∀ B : RealForm M 2, SmoothRealForm B → CompactlySupportedRealForm B →
      RealOneOne B → FormLE 0 B → 0 ≤ ∫ y, formInner g.form A B y ∂μ) :
    FormLE 0 A := by
  let : (lebesgueC n).IsAddHaarMeasure := by
    rw [lebesgueC_eq_volume]
    infer_instance
  intro c
  rw [formHermitianMatrix_zero, sub_zero]
  apply (matrix_posSemidef_iff_metric_trace_tests (gMat g.form c)
    (formHermitianMatrix A c)
    (L12Aux.hMat_posDef g.form c (chartPt c c) (mem_extChartAt_target c))
    ((representsSelf A h11A).2 c)).mpr
  intro D hD
  have hp : 0 ≤ chartPairDensity g.form A c D (chartPt c c) := by
    apply nonnegative_of_compact_tests (lebesgueC n)
      (isOpen_extChartAt_target (I := ComplexModel n) c)
      (chartPairDensity g.form A c D) (chartPairDensity_continuousOn g A hsA c D)
      ?_ (mem_extChartAt_target c)
    intro φ hφ hcφ hφO hφpos
    obtain ⟨hB, hcB, _⟩ := chartPositiveTest_properties c φ hφ hcφ hφO D hD.1
    have hb := ht (chartPositiveTest c φ D hD.1) hB hcB
      (chartPositiveTest_oneOne c φ D hD.1)
      (chartPositiveTest_nonnegative c φ hφpos D hD)
    rwa [integral_chartPositiveTest g μ hμ A hsA h11A c φ hφ hcφ hφO D hD.1] at hb
  rw [chartPairDensity, chartHermitianMatrix_center] at hp
  exact nonneg_of_mul_nonneg_right hp
    (L12Aux.volumeDensity_pos g.form c (chartPt c c) (mem_extChartAt_target c))

/-- The compact positive current inequality gives the literal pointwise
upper Levi bound, with the original iota and trace normalizations. -/
theorem smooth_levi_upper_of_compact_positive_tests
    (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ)
    (hf : SmoothFn f) (C : ℝ)
    (ht : ∀ B : RealForm M 2, SmoothRealForm B → CompactlySupportedRealForm B →
      RealOneOne B → FormLE 0 B →
      (∫ y, formInner g.form (ddRealForm f) B y ∂μ) ≤
        C * ∫ y, formTrace g.form B y ∂μ) :
    ∀ x, HermLE (levi f x) ((C : ℂ) • gMat g.form x) := by
  let A : RealForm M 2 := C • omegaForm g.form - ddRealForm f
  have hω : SmoothRealForm (omegaForm g.form) :=
    omegaForm_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g)
  have hdd := dd_properties f hf
  have hsA : SmoothRealForm A := by
    have hn : (-1 : ℝ) • ddRealForm f = -ddRealForm f := by
      funext y
      apply ContinuousAlternatingMap.ext
      intro V
      change (-1 : ℝ) * ddRealForm f y V = -ddRealForm f y V
      ring
    simpa only [A, sub_eq_add_neg, hn] using
      smoothRealForm_add (C • omegaForm g.form) ((-1 : ℝ) • ddRealForm f)
        (smoothRealForm_smul C _ hω) (smoothRealForm_smul (-1) _ hdd.1)
  have h11A : RealOneOne A := realOneOne_sub _ _
    (realOneOne_multiply (fun _ => C) _ (omegaForm_oneOne g.form)) hdd.2.1
  have hp : FormLE 0 A := by
    apply smooth_formLE_of_compact_positive_tests g μ hμ A hsA h11A
    intro B hsB hcB h11B hpB
    have hddI : Integrable (formInner g.form (ddRealForm f) B) μ := by
      rw [formInner_symm g.form (ddRealForm f) B]
      exact smooth_compact_formInner_integrable g μ hμ B _ hsB hdd.1 hcB
    have htrI := smooth_compact_formInner_integrable g μ hμ B (omegaForm g.form) hsB hω hcB
    have htrEq : formInner g.form B (omegaForm g.form) = formTrace g.form B :=
      funext (formInner_omegaForm g.form B h11B)
    rw [htrEq] at htrI
    have heq : formInner g.form A B = fun y =>
        C * formTrace g.form B y - formInner g.form (ddRealForm f) B y := by
      funext y
      rw [show A = C • omegaForm g.form - ddRealForm f from rfl,
        formInner_sub_left, formInner_smul_left]
      change C * formInner g.form (omegaForm g.form) B y -
        formInner g.form (ddRealForm f) B y = _
      rw [formInner_symm g.form (omegaForm g.form) B,
        formInner_omegaForm g.form B h11B y]
    rw [heq, integral_sub (htrI.const_mul C) hddI, integral_const_mul]
    exact sub_nonneg.mpr (ht B hsB hcB h11B hpB)
  intro x
  have hx := hp x
  change ((C : ℂ) • gMat g.form x - levi f x).PosSemidef
  simpa only [A, formHermitianMatrix_zero, sub_zero, formHermitianMatrix_sub,
    formHermitianMatrix_real_smul,
    formHermitianMatrix_of_representsIota _ _ (omegaForm_represents g.form),
    formHermitianMatrix_of_representsIota _ _ hdd.2.2.2] using hx

end Yau.NodeProofs.P06Aux.CurrentSeparation
