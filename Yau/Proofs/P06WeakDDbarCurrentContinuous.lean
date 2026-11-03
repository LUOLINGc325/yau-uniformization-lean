import Yau.Proofs.P06WeakDDbarCurrentChartIntegrals

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux.WeakCurrent
open Yau Yau.Blueprint Yau.LeafProofs Yau.LeafProofs.L03 Yau.NodeProofs.G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem leviMatrixTestDual_regular {O : Set (ComplexVector n)}
    (B : ComplexVector n → Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun z => B z i j))
    (hcB : ∀ i j, HasCompactSupport (fun z => B z i j))
    (hBO : ∀ i j, tsupport (fun z => B z i j) ⊆ O) :
    ContDiff ℝ ∞ (leviMatrixTestDual B) ∧ HasCompactSupport (leviMatrixTestDual B) ∧
      tsupport (leviMatrixTestDual B) ⊆ O := by
  classical
  have hreg := hermitianTestCoefficients_regular B hB hcB hBO
  let K := ⋃ p : (Fin n × Fin n) × Fin 4,
    tsupport (fun z => hermitianTestCoefficients (B z) p)
  have hK : IsCompact K := isCompact_iUnion (fun p => (hreg p).2.1)
  have hKO : K ⊆ O := Set.iUnion_subset (fun p => (hreg p).2.2)
  have hs : tsupport (leviMatrixTestDual B) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hn
    have hzero (p : (Fin n × Fin n) × Fin 4) :
        leviDirection (leviC (fun w => hermitianTestCoefficients (B w) p) z)
          (hermitianTestVectors n p) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
        (f := fun z => leviDirection (leviC (fun w => hermitianTestCoefficients (B w) p) z)
          (hermitianTestVectors n p))
      intro h
      exact hn (Set.mem_iUnion.mpr ⟨p,
        (leviDirection_hasCompactSupport _ (hreg p).2.1 (hermitianTestVectors n p)).2 h⟩)
    exact hz (by simp only [leviMatrixTestDual, hzero, Finset.sum_const_zero])
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans hKO⟩
  apply ContDiff.sum
  intro p _
  exact contDiffOn_univ.mp (leviDirection_contDiffOn isOpen_univ (hreg p).1.contDiffOn
    (hermitianTestVectors n p))

theorem integral_mul_uniform_error {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f F q : α → ℝ) (hf : Integrable (fun x => f x * q x) μ)
    (hF : Integrable (fun x => F x * q x) μ) (hq : Integrable (fun x => |q x|) μ)
    {ε : ℝ} (herr : ∀ x, |F x - f x| ≤ ε) :
    |(∫ x, f x * q x ∂μ) - ∫ x, F x * q x ∂μ| ≤ ε * ∫ x, |q x| ∂μ := by
  rw [← integral_sub hf hF]
  have h := norm_integral_le_of_norm_le (f := fun x => f x * q x - F x * q x)
    (hq.const_mul ε) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_sub_comm]
      exact mul_le_mul_of_nonneg_right (herr x) (abs_nonneg _))
  rw [integral_const_mul] at h
  exact h

/-- The coordinate matrix-dual identity extends to every continuous scalar
input. Only smooth approximants are differentiated. -/
theorem integral_continuous_chart_dual (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ) (hf : Continuous f)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (h11 : RealOneOne B) (hp : FormLE 0 B) (c : M.Carrier)
    (hBc : closure {y | B y ≠ 0} ⊆ (extChartAt (ComplexModel n) c).source) :
    (∫ y, f y * ddAdjointScalar g.form B y ∂μ) =
      ∫ z, inChart c f z * leviMatrixTestDual (chartMatrixTest g.form B c) z ∂lebesgueC n := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  letI : (lebesgueC n).IsAddHaarMeasure := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]; infer_instance
  letI := L12Aux.manifold_realSmooth M
  letI : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  let q₁ := ddAdjointScalar g.form B
  let q₂ := leviMatrixTestDual (chartMatrixTest g.form B c)
  have hq₁ : Continuous q₁ := L18Aux.continuous_of_smoothFn (ddAdjointScalar_smooth g μ hμ B hB)
  have hcq₁ : HasCompactSupport q₁ := ddAdjointScalar_compact g μ hμ B hB hcB
  have hr := chartMatrixTest_regular g B hB hcB c hBc
  have hq₂r := leviMatrixTestDual_regular (chartMatrixTest g.form B c)
    (fun a b => (hr a b).1) (fun a b => (hr a b).2.1) (fun a b => (hr a b).2.2)
  have hq₂ : Continuous q₂ := hq₂r.1.continuous
  have hcq₂ : HasCompactSupport q₂ := hq₂r.2.1
  have hq₂O : tsupport q₂ ⊆ chartTarget c := hq₂r.2.2
  have hO : IsOpen (chartTarget c) := isOpen_extChartAt_target (I := ComplexModel n) c
  have hfi₁ : Integrable (fun y => f y * q₁ y) μ :=
    (hf.mul hq₁).integrable_of_hasCompactSupport hcq₁.mul_left
  have hfi₂ : Integrable (fun z => inChart c f z * q₂ z) (lebesgueC n) := by
    simpa only [mul_comm, inChart, chartInv, Function.comp_def] using L18Aux.integrable_compactTest_mul (lebesgueC n) hO hq₂ hcq₂ hq₂O
      (hf.comp_continuousOn (continuousOn_extChartAt_symm (I := ComplexModel n) c))
  have hi₁ : Integrable (fun y => |q₁ y|) μ := (hq₁.integrable_of_hasCompactSupport hcq₁).abs
  have hi₂ : Integrable (fun z => |q₂ z|) (lebesgueC n) := (hq₂.integrable_of_hasCompactSupport hcq₂).abs
  let R := (∫ y, |q₁ y| ∂μ) + ∫ z, |q₂ z| ∂lebesgueC n
  have hR : 0 ≤ R := add_nonneg (integral_nonneg (fun _ => abs_nonneg _))
    (integral_nonneg (fun _ => abs_nonneg _))
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (R + 1)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨F, hFclose, _⟩ := hf.exists_contMDiff_approx 𝓘(ℝ, ComplexVector n) ⊤
    (ε := fun _ => δ) continuous_const (fun _ => hδ)
  have hFs : SmoothFn (fun x => F x) := L12Aux.smoothFn_of_contMDiff_real _ F.contMDiff
  have hFc : Continuous (fun x => F x) := F.contMDiff.continuous
  have hclose (x : M.Carrier) : |F x - f x| ≤ δ := by
    simpa only [Real.dist_eq] using (hFclose x).le
  have hFi₁ : Integrable (fun y => F y * q₁ y) μ :=
    (hFc.mul hq₁).integrable_of_hasCompactSupport hcq₁.mul_left
  have hFi₂ : Integrable (fun z => inChart c (fun y => F y) z * q₂ z) (lebesgueC n) := by
    simpa only [mul_comm, inChart, chartInv, Function.comp_def] using L18Aux.integrable_compactTest_mul (lebesgueC n) hO hq₂ hcq₂ hq₂O
      (hFc.comp_continuousOn (continuousOn_extChartAt_symm (I := ComplexModel n) c))
  have he := integral_dd_chart_dual g μ hμ (fun y => F y) hFs B hB hcB h11 hp c hBc
  have he₁ := integral_mul_uniform_error μ f (fun y => F y) q₁ hfi₁ hFi₁ hi₁ hclose
  have he₂ := integral_mul_uniform_error (lebesgueC n) (inChart c f)
    (inChart c (fun y => F y)) q₂ hfi₂ hFi₂ hi₂ (fun z => hclose (chartInv c z))
  have hbound : |(∫ y, f y * q₁ y ∂μ) - ∫ z, inChart c f z * q₂ z ∂lebesgueC n| ≤ δ * R := by
    calc
      _ ≤ |(∫ y, f y * q₁ y ∂μ) - ∫ y, F y * q₁ y ∂μ| +
          |(∫ y, F y * q₁ y ∂μ) - ∫ z, inChart c f z * q₂ z ∂lebesgueC n| := abs_sub_le _ _ _
      _ = |(∫ y, f y * q₁ y ∂μ) - ∫ y, F y * q₁ y ∂μ| +
          |(∫ z, inChart c f z * q₂ z ∂lebesgueC n) -
            ∫ z, inChart c (fun y => F y) z * q₂ z ∂lebesgueC n| := by
        change _ = _
        rw [show (∫ y, F y * q₁ y ∂μ) = ∫ z, inChart c (fun y => F y) z * q₂ z ∂lebesgueC n from he,
          abs_sub_comm (∫ z, inChart c (fun y => F y) z * q₂ z ∂lebesgueC n)]
      _ ≤ δ * R := by dsimp only [R]; nlinarith [he₁, he₂]
  have hδε : δ * (R + 1) = ε := by dsimp only [δ]; field_simp
  change _ ≤ 0 + ε
  exact hbound.trans (by nlinarith)

/-- The original weak Levi upper bound controls each genuine positive
compact smooth real (1,1) test supported in one chart. -/
theorem weakLeviUpper_chart_test (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ) (hf : Continuous f)
    (C : ℝ) (hc : ConstantOutsideCompact f) (hw : WeakLeviUpper g.form f C)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (h11 : RealOneOne B) (hp : FormLE 0 B) (c : M.Carrier)
    (hBc : closure {y | B y ≠ 0} ⊆ (extChartAt (ComplexModel n) c).source) :
    (∫ y, f y * ddAdjointScalar g.form B y ∂μ) ≤ C * ∫ y, formTrace g.form B y ∂μ := by
  rw [integral_continuous_chart_dual g μ hμ f hf B hB hcB h11 hp c hBc]
  have hr := chartMatrixTest_regular g B hB hcB c hBc
  have he := weakLeviUpper_positive_matrix_test g f hf C hc hw c
    (chartMatrixTest g.form B c) (fun a b => (hr a b).1) (fun a b => (hr a b).2.1)
    (fun a b => (hr a b).2.2) (chartMatrixTest_nonnegative g.form B h11 hp c)
  rw [integral_chartMatrixTest_trace g μ hμ B hB hcB h11 c hBc] at he
  exact he

end Yau.NodeProofs.P06Aux.WeakCurrent
