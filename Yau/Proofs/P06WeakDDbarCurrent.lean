import Yau.Proofs.P06WeakDDbarCurrentContinuous
import Yau.Proofs.P06WeakDDbarCurrentLinearity

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux.WeakCurrent
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03 Yau.NodeProofs.G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem currentPairing_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ) (hf : Continuous f)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    Integrable (fun y => f y * ddAdjointScalar g.form B y) μ := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  have hq := L18Aux.continuous_of_smoothFn (ddAdjointScalar_smooth g μ hμ B hB)
  exact (hf.mul hq).integrable_of_hasCompactSupport
    (ddAdjointScalar_compact g μ hμ B hB hcB).mul_left

theorem formTrace_integrable (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) (h11 : RealOneOne B) :
    Integrable (formTrace g.form B) μ := by
  have he : formTrace g.form B = formInner g.form B (omegaForm g.form) :=
    funext (formTrace_eq_inner_omega g.form B h11)
  rw [he]
  exact smooth_compact_formInner_integrable g μ hμ B _ hB
    (omegaForm_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g)) hcB

/-- The literal original weak Levi bound is the global current inequality
against every genuine compact smooth positive real (1,1) form. -/
theorem weakLeviUpper_global_test (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ) (hf : Continuous f)
    (C : ℝ) (hc : ConstantOutsideCompact f) (hw : WeakLeviUpper g.form f C)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (h11 : RealOneOne B) (hp : FormLE 0 B) :
    (∫ y, f y * ddAdjointScalar g.form B y ∂μ) ≤ C * ∫ y, formTrace g.form B y ∂μ := by
  classical
  obtain ⟨s, p, hpsmooth, hpnonneg, hpsource, hpsum⟩ := L18Aux.exists_finite_smooth_partition hcB
  let Bs : s → RealForm M 2 := fun i => multiplyRealForm (p i) B
  have hsB (i : s) : SmoothRealForm (Bs i) := smoothRealForm_multiply _ B (hpsmooth i) hB
  have hcBs (i : s) : CompactlySupportedRealForm (Bs i) := compactlySupportedRealForm_multiply _ B hcB
  have hBsources (i : s) : closure {y | Bs i y ≠ 0} ⊆
      (extChartAt (ComplexModel n) (i : M.Carrier)).source :=
    (multiplyRealForm_support_subset_scalar _ B).trans (hpsource i)
  have h11Bs (i : s) : RealOneOne (Bs i) := by
    intro x u v
    change p i x * B x ![Complex.I • u, Complex.I • v] = p i x * B x ![u,v]
    rw [h11 x u v]
  have hpBs (i : s) : FormLE 0 (Bs i) := by
    intro x
    rw [formHermitianMatrix_zero, sub_zero]
    have he : formHermitianMatrix (Bs i) x = formHermitianMatrix ((p i x) • B) x := rfl
    rw [he, formHermitianMatrix_real_smul]
    have hpx : (formHermitianMatrix B x).PosSemidef := by
      simpa only [formHermitianMatrix_zero, sub_zero] using hp x
    exact hpx.smul (by exact_mod_cast hpnonneg i x)
  have hsumB : (∑ i, Bs i) = B := by
    funext y
    simp only [Finset.sum_apply, Bs, multiplyRealForm]
    rw [← Finset.sum_smul]
    by_cases hy : B y = 0
    · simp only [hy, smul_zero]
    · rw [hpsum y (subset_closure hy), one_smul]
  have hsumadj (y : M.Carrier) : ddAdjointScalar g.form B y = ∑ i, ddAdjointScalar g.form (Bs i) y := by
    rw [← hsumB, ddAdjointScalar_fintypeSum g μ hμ Bs hsB]
    simp only [Finset.sum_apply]
  have hsumtrace (y : M.Carrier) : (∑ i, formTrace g.form (Bs i) y) = formTrace g.form B y := by
    calc
      _ = ∑ i, formInner g.form (Bs i) (omegaForm g.form) y :=
        Finset.sum_congr rfl (fun i _ => formTrace_eq_inner_omega g.form (Bs i) (h11Bs i) y)
      _ = formInner g.form (∑ i, Bs i) (omegaForm g.form) y :=
        (formInner_fintypeSum_left g.form Bs _ y).symm
      _ = formTrace g.form B y := by rw [hsumB, ← formTrace_eq_inner_omega g.form B h11]
  have hiadj (i : s) := currentPairing_integrable g μ hμ f hf (Bs i) (hsB i) (hcBs i)
  have hitrace (i : s) := formTrace_integrable g μ hμ (Bs i) (hsB i) (hcBs i) (h11Bs i)
  calc
    _ = ∫ y, ∑ i, f y * ddAdjointScalar g.form (Bs i) y ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hsumadj, Finset.mul_sum]
    _ = ∑ i, ∫ y, f y * ddAdjointScalar g.form (Bs i) y ∂μ :=
      integral_finsetSum Finset.univ (fun i _ => hiadj i)
    _ ≤ ∑ i, C * ∫ y, formTrace g.form (Bs i) y ∂μ := by
      apply Finset.sum_le_sum
      intro i _
      exact weakLeviUpper_chart_test g μ hμ f hf C hc hw (Bs i) (hsB i) (hcBs i)
        (h11Bs i) (hpBs i) (i : M.Carrier) (hBsources i)
    _ = C * ∫ y, ∑ i, formTrace g.form (Bs i) y ∂μ := by
      rw [← Finset.mul_sum, integral_finsetSum Finset.univ (fun i _ => hitrace i)]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hsumtrace

/-- The original Lipschitz data supply continuity internally. -/
theorem weakLeviUpper_lipschitz_global_test (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ)
    (hf : LipschitzForMetric g.form f) (C : ℝ) (hc : ConstantOutsideCompact f)
    (hw : WeakLeviUpper g.form f C) (B : RealForm M 2) (hB : SmoothRealForm B)
    (hcB : CompactlySupportedRealForm B) (h11 : RealOneOne B) (hp : FormLE 0 B) :
    (∫ y, f y * ddAdjointScalar g.form B y ∂μ) ≤ C * ∫ y, formTrace g.form B y ∂μ :=
  weakLeviUpper_global_test g μ hμ f (continuous_of_metricLipschitz g hf) C hc hw B hB hcB h11 hp

end Yau.NodeProofs.P06Aux.WeakCurrent
