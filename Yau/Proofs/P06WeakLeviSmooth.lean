import Yau.Proofs.P06LeviTests

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff ComplexOrder

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L18Aux

theorem nonnegative_of_compact_tests {n : ℕ} (ν : Measure (ComplexVector n)) [ν.IsAddHaarMeasure]
    {O : Set (ComplexVector n)} (hO : IsOpen O) (F : ComplexVector n → ℝ)
    (hF : ContinuousOn F O)
    (htest : ∀ φ : ComplexVector n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O → (∀ w, 0 ≤ φ w) → 0 ≤ ∫ w, φ w * F w ∂ν)
    {z : ComplexVector n} (hz : z ∈ O) : 0 ≤ F z := by
  by_contra hn
  have hneg : F z < 0 := lt_of_not_ge hn
  have hV : {w | w ∈ O ∧ F w < 0} ∈ 𝓝 z :=
    inter_mem (hO.mem_nhds hz) ((hF.continuousAt (hO.mem_nhds hz)).eventually (Iio_mem_nhds hneg))
  obtain ⟨φ, hφV, hcφ, hφ, hφrange, hφz⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hV
  have hφO : tsupport φ ⊆ O := fun w hw => (hφV hw).1
  have hφnonneg : ∀ w, 0 ≤ φ w := fun w => (hφrange ⟨w, rfl⟩).1
  have hi : Integrable (fun w => φ w * F w) ν :=
    integrable_compactTest_mul ν hO hφ.continuous hcφ hφO hF
  have hnp (w : ComplexVector n) : φ w * F w ≤ 0 := by
    by_cases hφw : φ w = 0
    · simp only [hφw, zero_mul, le_refl]
    · exact mul_nonpos_of_nonneg_of_nonpos (hφnonneg w) (hφV (subset_closure hφw)).2.le
  have hzero : (∫ w, φ w * F w ∂ν) = 0 :=
    le_antisymm (integral_nonpos hnp) (htest φ hφ hcφ hφO hφnonneg)
  have hnegzero : (∫ w, -(φ w * F w) ∂ν) = 0 := by rw [integral_neg, hzero, neg_zero]
  have hae := (integral_eq_zero_iff_of_nonneg (fun w => neg_nonneg.mpr (hnp w)) hi.neg).mp hnegzero
  have hae' : (fun w => φ w * F w) =ᵐ[ν] 0 := by
    filter_upwards [hae] with w hw
    exact neg_eq_zero.mp hw
  have hc : ContinuousOn (fun w => φ w * F w) O := hφ.continuous.continuousOn.mul hF
  have hv : φ z * F z = 0 :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae') hO hc continuousOn_const hz
  rw [hφz, one_mul] at hv
  linarith

theorem leviDirection_contDiffOn {n : ℕ} {O : Set (ComplexVector n)} (hO : IsOpen O)
    {u : ComplexVector n → ℝ} (hu : ContDiffOn ℝ ∞ u O) (v : ComplexVector n) :
    ContDiffOn ℝ ∞ (fun z => leviDirection (leviC u z) v) O := by
  have hd := ((direction_contDiffOn hO (direction_contDiffOn hO hu v) v).add
    (direction_contDiffOn hO (direction_contDiffOn hO hu (Complex.I • v)) (Complex.I • v))).div_const 4
  apply hd.congr
  intro z hz
  exact leviDirection_eq_second ((hu.contDiffAt (hO.mem_nhds hz)).of_le (by simp)) v

theorem metricLeviDirection_contDiffOn {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (x : M.Carrier) (v : ComplexVector n) :
    ContDiffOn ℝ ∞ (fun z => leviDirection (hMat g.form x z) v) (chartTarget x) := by
  apply Complex.reCLM.contDiff.comp_contDiffOn
  unfold dotProduct Matrix.mulVec
  apply ContDiffOn.sum
  intro i _
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro j _
  exact (hMat_contDiffOn g x i j).mul contDiffOn_const

/-- In the smooth case the literal weak constant-direction tests imply
the classical inequality in every actual chart. -/
theorem weakLeviUpper_classical_on {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (C : ℝ)
    (hw : WeakLeviUpper g.form f C) (x : M.Carrier) (v : ComplexVector n)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hOt : O ⊆ chartTarget x)
    (hf : ContDiffOn ℝ ∞ (inChart x f) O) {z : ComplexVector n} (hz : z ∈ O) :
    leviDirection (leviC (inChart x f) z) v ≤ C * leviDirection (hMat g.form x z) v := by
  letI : (lebesgueC n).IsAddHaarMeasure := by rw [Yau.LeafProofs.lebesgueC_eq_volume]; infer_instance
  have hL := leviDirection_contDiffOn hO hf v
  have hG := (metricLeviDirection_contDiffOn g x v).mono hOt
  let F : ComplexVector n → ℝ := fun w => C * leviDirection (hMat g.form x w) v -
    leviDirection (leviC (inChart x f) w) v
  have hF : ContinuousOn F O := (continuousOn_const.mul hG.continuousOn).sub hL.continuousOn
  have hpos : 0 ≤ F z := by
    apply nonnegative_of_compact_tests (lebesgueC n) hO F hF ?_ hz
    intro φ hφ hcφ hφO hφnonneg
    obtain ⟨_, hiG, hineq⟩ := hw x v φ hφ hcφ (hφO.trans hOt) hφnonneg
    have hiL := integrable_compactTest_mul (lebesgueC n) hO hφ.continuous hcφ hφO hL.continuousOn
    have hparts := integral_leviDirection_test hO hφ hcφ hφO hf v
    rw [hparts] at hineq
    have heq : (fun w => φ w * F w) =
        (fun w => C * (φ w * leviDirection (hMat g.form x w) v) -
          φ w * leviDirection (leviC (inChart x f) w) v) := by
      funext w
      dsimp only [F]
      ring
    rw [heq, integral_sub (hiG.const_mul C) hiL, integral_const_mul]
    linarith
  exact sub_nonneg.mp hpos

theorem weakLeviUpper_classical_chart {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (hf : SmoothFn f) (C : ℝ)
    (hw : WeakLeviUpper g.form f C) (x : M.Carrier) (v : ComplexVector n)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    leviDirection (leviC (inChart x f) z) v ≤ C * leviDirection (hMat g.form x z) v :=
  weakLeviUpper_classical_on g f C hw x v
    (isOpen_extChartAt_target (I := ComplexModel n) x) Set.Subset.rfl (hf x) hz

/-- The original weak upper Levi bound recovers the original Hermitian
matrix order for every smooth datum, including zero directions. -/
theorem weakLeviUpper_classical {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (f : M.Carrier → ℝ) (hf : SmoothFn f) (C : ℝ)
    (hw : WeakLeviUpper g.form f C) (x : M.Carrier) :
    HermLE (levi f x) ((C : ℂ) • gMat g.form x) := by
  have hG := Yau.LeafProofs.L12Aux.hMat_isHermitian g.form x (chartPt x x)
  have hH : ((C : ℂ) • gMat g.form x - levi f x).IsHermitian :=
    (hG.smul (by simp [IsSelfAdjoint])).sub (G04Aux.levi_hermitian f hf x)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self v).symm⟩
  have h := weakLeviUpper_classical_chart g f hf C hw x (WithLp.toLp 2 v) (mem_extChartAt_target x)
  simpa only [leviDirection, WithLp.ofLp_toLp, Matrix.sub_mulVec, Matrix.smul_mulVec,
    dotProduct_sub, dotProduct_smul, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul, levi, gMat, chartPt] using sub_nonneg.mpr h

end Yau.NodeProofs.P06Aux
