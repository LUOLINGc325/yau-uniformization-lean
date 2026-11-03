import Yau.Proofs.F03CompactGreenTransfer
import Yau.Proofs.F03GradientPairNorm

/-! The exact compact Green transfer has a quantitative error using only an integrable first-gradient envelope. -/
noncomputable section
open MeasureTheory Set
namespace Yau.Proofs.F03Aux
open Yau Blueprint LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem integral_compact_green_error_le
    (g : SmoothMetric M) (hK : IsKahler g)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    {v k χ E : M.Carrier → ℝ} (hv : SmoothFn v) (hk : SmoothFn k)
    (hχ : SmoothFn χ) (hcχ : HasCompactSupport χ) (o : M.Carrier)
    {R : ℝ} (hR : 0 < R) (hsχ : tsupport χ ⊆ distBall g.form o R)
    (hRange : ∀ y,χ y ∈ Icc (0:ℝ) 1)
    (hE : Integrable E μ) (hE0 : ∀ y,0 ≤ E y)
    (hEnvelope : ∀ y,|v y*k y| ≤ E y ∧
      |v y| * Real.sqrt (gradNormSq g.form k y) ≤ E y ∧
      |k y*laplacian g.form v y| ≤ E y)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hLap : ∀ y,|laplacian g.form χ y| ≤ a)
    (hGrad : ∀ y,Real.sqrt (gradNormSq g.form χ y) ≤ b) :
    |(∫ y,k y*laplacian g.form (fun z => χ z*v z) y ∂μ)-
      (∫ y,k y*laplacian g.form v y ∂μ)| ≤
      (∫ y,(1-χ y)*E y ∂μ)+(a+2*b)*(∫ y,E y ∂μ) := by
  have hG := integral_laplacian_compact_product_transfer g hK μ hμ hv hk hχ hcχ o hR hsχ
  have hMain : Integrable (fun y => k y*laplacian g.form v y) μ :=
    hE.mono' (continuous_of_smoothFn (smoothFn_mul hk (smoothFn_laplacian g hv))).aestronglyMeasurable
      (ae_of_all μ (fun y => by simpa only [Real.norm_eq_abs] using (hEnvelope y).2.2))
  have hRest : Integrable (fun y => (1-χ y)*E y) μ := by
    apply hE.mono' ((continuous_const.sub (continuous_of_smoothFn hχ)).aestronglyMeasurable.mul hE.aestronglyMeasurable)
    apply ae_of_all μ
    intro y
    change |(1-χ y)*E y| ≤ E y
    rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hRange y).2),abs_of_nonneg (hE0 y)]
    exact mul_le_of_le_one_left (hE0 y) (by linarith [(hRange y).1])
  have hMainError : |(∫ y,k y*χ y*laplacian g.form v y ∂μ)-
      (∫ y,k y*laplacian g.form v y ∂μ)| ≤ ∫ y,(1-χ y)*E y ∂μ := by
    rw [← integral_sub hG.2.1 hMain]
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hRest
    apply ae_of_all μ
    intro y
    change |k y*χ y*laplacian g.form v y-k y*laplacian g.form v y| ≤ _
    have hEq : k y*χ y*laplacian g.form v y-k y*laplacian g.form v y=
        -(1-χ y)*(k y*laplacian g.form v y) := by ring
    rw [hEq,abs_mul,abs_neg,abs_of_nonneg (sub_nonneg.mpr (hRange y).2)]
    exact mul_le_mul_of_nonneg_left (hEnvelope y).2.2 (sub_nonneg.mpr (hRange y).2)
  have hLapError : |∫ y,v y*k y*laplacian g.form χ y ∂μ| ≤ a*(∫ y,E y ∂μ) := by
    have hBound : |∫ y,v y*k y*laplacian g.form χ y ∂μ| ≤ ∫ y,a*E y ∂μ := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hE.const_mul a)
      apply ae_of_all μ
      intro y
      change |v y*k y*laplacian g.form χ y| ≤ _
      rw [abs_mul]
      convert mul_le_mul (hEnvelope y).1 (hLap y) (abs_nonneg _) (hE0 y) using 1 <;> ring
    simpa only [integral_const_mul] using hBound
  have hGradError : |∫ y,v y*scalarGradientPair g.form k χ y ∂μ| ≤ (2*b)*(∫ y,E y ∂μ) := by
    have hBound : |∫ y,v y*scalarGradientPair g.form k χ y ∂μ| ≤ ∫ y,(2*b)*E y ∂μ := by
      rw [← Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hE.const_mul (2*b))
      apply ae_of_all μ
      intro y
      change |v y*scalarGradientPair g.form k χ y| ≤ _
      rw [abs_mul]
      calc
        _ ≤ |v y| * (2*Real.sqrt (gradNormSq g.form k y)*Real.sqrt (gradNormSq g.form χ y)) :=
          mul_le_mul_of_nonneg_left (abs_scalarGradientPair_le g.form hk hχ y) (abs_nonneg _)
        _ = 2*(|v y| * Real.sqrt (gradNormSq g.form k y))*Real.sqrt (gradNormSq g.form χ y) := by ring
        _ ≤ 2*E y*b := mul_le_mul (mul_le_mul_of_nonneg_left (hEnvelope y).2.1 (by norm_num))
          (hGrad y) (Real.sqrt_nonneg _) (mul_nonneg (by norm_num) (hE0 y))
        _ = _ := by ring
    simpa only [integral_const_mul] using hBound
  rw [hG.2.2.2.2]
  calc
    _ = |((∫ y,k y*χ y*laplacian g.form v y ∂μ)-(∫ y,k y*laplacian g.form v y ∂μ))-
        (∫ y,v y*k y*laplacian g.form χ y ∂μ)-(∫ y,v y*scalarGradientPair g.form k χ y ∂μ)| := by congr 1;ring
    _ ≤ |(∫ y,k y*χ y*laplacian g.form v y ∂μ)-(∫ y,k y*laplacian g.form v y ∂μ)|+
        |∫ y,v y*k y*laplacian g.form χ y ∂μ|+|∫ y,v y*scalarGradientPair g.form k χ y ∂μ| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by linarith

end Yau.Proofs.F03Aux
