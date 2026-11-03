import Yau.LeafProofs.L17SourceLocalizationGlobal

/-! Literal parabolic rescaling of the actual total forcing, exported in
the exact ComplexVector-based HolderBound used by the Gaussian kernel API. -/

open Set Metric
noncomputable section
namespace Yau.LeafProofs.L17SourceLocalizationAux
open L17Aux L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def rescaledSource (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Yau.Parabolic.Point n) : ℝ :=
  localizedSource P T hT f p (P.radius • q.1,P.radius ^ 2 * q.2)

theorem rescaledSource_continuous (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) : Continuous (rescaledSource P T hT f p) :=
  (localizedSource_continuous P T hT f p).comp
    ((continuous_fst.const_smul P.radius).prodMk (continuous_const.mul continuous_snd))

theorem rescaledSource_abs_le_norm (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Yau.Parabolic.Point n) :
    |rescaledSource P T hT f p q| ≤ ‖f‖ := localizedSource_abs_le_norm P T hT f p _

theorem parabolicDistance_scale (ρ : ℝ) (hρ : 0 < ρ) (q r : Yau.Parabolic.Point n) :
    Yau.Parabolic.parabolicDistance (ρ • q.1,ρ ^ 2 * q.2) (ρ • r.1,ρ ^ 2 * r.2) =
      ρ * Yau.Parabolic.parabolicDistance q r := by
  simp only [Yau.Parabolic.parabolicDistance, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos hρ, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg ρ),
    Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq_eq_abs, abs_of_pos hρ]
  ring

theorem rescaledSource_difference (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ K : ℝ} (hγ : 0 ≤ γ) (hK : 0 ≤ K) (f η : HolderSpace P T γ) (p : P.centers)
    (hη : ∀ x, holderFun η x = P.weight p x.1) (hηK : ‖η‖ ≤ K)
    (q r : Yau.Parabolic.Point n) :
    |rescaledSource P T hT f p r - rescaledSource P T hT f p q| ≤
      sourceHolderConstant K γ * ‖f‖ * Yau.Parabolic.parabolicDistance q r ^ γ := by
  have hh := localizedSource_global_difference P T hT hγ hK f η p hη hηK
    (P.radius • q.1,P.radius ^ 2 * q.2) (P.radius • r.1,P.radius ^ 2 * r.2)
  rw [parabolicDistance_scale P.radius P.radius_pos] at hh
  have hDiv : (P.radius * Yau.Parabolic.parabolicDistance q r) / P.radius =
      Yau.Parabolic.parabolicDistance q r := by field_simp [P.radius_pos.ne']
  rw [hDiv] at hh
  exact hh

theorem rescaledSource_holderBound (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ K : ℝ} (hγ : 0 ≤ γ) (hK : 0 ≤ K) (f η : HolderSpace P T γ) (p : P.centers)
    (hη : ∀ x, holderFun η x = P.weight p x.1) (hηK : ‖η‖ ≤ K) :
    Yau.Parabolic.HolderBound γ Set.univ (rescaledSource P T hT f p)
      ((sourceHolderConstant K γ * (2 : ℝ) ^ γ) * ‖f‖) := by
  have hC := sourceHolderConstant_bounds hK hγ
  have hPow : (1 : ℝ) ≤ 2 ^ γ := Real.one_le_rpow (by norm_num) hγ
  have hCOne : 1 ≤ sourceHolderConstant K γ := hPow.trans hC.2.2
  have hProduct : 1 ≤ sourceHolderConstant K γ * (2 : ℝ) ^ γ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hCOne) (sub_nonneg.mpr hPow)]
  refine ⟨by positivity, ?_, ?_⟩
  · intro q _
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖f‖ := rescaledSource_abs_le_norm P T hT f p q
      _ = 1 * ‖f‖ := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hProduct (norm_nonneg f)
  · intro q _ r _
    rw [Real.norm_eq_abs, abs_sub_comm]
    have hDiff := rescaledSource_difference P T hT hγ hK f η p hη hηK q r
    exact hDiff.trans ((mul_le_mul_of_nonneg_left (parabolicDistance_rpow_le_holderWeight hγ q r)
      (mul_nonneg hC.1 (norm_nonneg f))).trans_eq (by ring))

theorem rescaledSource_add (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f h : HolderSpace P T γ) (p : P.centers) :
    rescaledSource P T hT (f + h) p = rescaledSource P T hT f p + rescaledSource P T hT h p := by
  funext q
  exact congrFun (localizedSource_add P T hT f h p) _

theorem rescaledSource_smul (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (c : ℝ) (f : HolderSpace P T γ) (p : P.centers) :
    rescaledSource P T hT (c • f) p = c • rescaledSource P T hT f p := by
  funext q
  exact congrFun (localizedSource_smul P T hT c f p) _

end Yau.LeafProofs.L17SourceLocalizationAux
