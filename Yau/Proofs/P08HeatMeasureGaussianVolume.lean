import Yau.Proofs.P08HeatMeasureMass

/-! The dimensional normalized Gaussian integral from the genuine Bishop--Gromov theorem. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff Manifold ComplexOrder InnerProductSpace
namespace Yau.NodeProofs.P08Aux.HeatMeasure
open LeafProofs LeafProofs.L19Aux LeafProofs.L18Aux LeafProofs.L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private def gaussianVolumeTerm (n j : ℕ) : ℝ :=
  ((j : ℝ) + 1) ^ (2 * n) * Real.exp (-((j : ℝ) ^ 2) / 2)

private theorem gaussianVolumeTerm_nonneg (n j : ℕ) : 0 ≤ gaussianVolumeTerm n j := by
  unfold gaussianVolumeTerm
  positivity

private theorem gaussianVolumeTerm_summable (n : ℕ) : Summable (gaussianVolumeTerm n) := by
  let C := Real.exp (((2 * n : ℕ) : ℝ) ^ 2)
  have hmajor : Summable (fun j : ℕ => C * Real.exp ((j : ℝ) * (-1 / 4))) :=
    (Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-1 / 4 : ℝ) < 0)).mul_left C
  apply hmajor.of_nonneg_of_le (gaussianVolumeTerm_nonneg n)
  intro j
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hs : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
    by_cases hz : j = 0
    · simp [hz]
    · have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      nlinarith
  have hp := polynomial_mul_gaussian_le (2 * n) (1 / 2) (by norm_num) (j : ℝ) hj
  have hp' : gaussianVolumeTerm n j ≤ C * Real.exp (-((j : ℝ) ^ 2) / 4) := by
    convert hp using 1 <;> dsimp [gaussianVolumeTerm, C] <;> congr 1 <;> ring
  apply hp'.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  linarith

/-- Chosen solely from the dimension, before all geometric and measure data. -/
def gaussianVolumeConstant (n : ℕ) : ℝ := (∑' j, gaussianVolumeTerm n j) + 1

theorem gaussianVolumeConstant_pos (n : ℕ) : 0 < gaussianVolumeConstant n := by
  dsimp [gaussianVolumeConstant]
  have hnonneg : (0 : ℝ) ≤ ∑' j, gaussianVolumeTerm n j := tsum_nonneg (gaussianVolumeTerm_nonneg n)
  linarith

/-- The normalized Gaussian integral, proved using measurable annuli and volume comparison. -/
theorem normalizedGaussianLIntegral (g : SmoothMetric M) (hcomplete : IsComplete g)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (L : ℝ) (hL : 0 < L) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-(distFrom g.form o y ^ 2) / (2 * L ^ 2))) ∂μ) ≤
      ENNReal.ofReal (gaussianVolumeConstant n) * μ (distBall g.form o L) := by
  let r := distFrom g.form o
  let A : ℕ → Set M.Carrier := fun j => {y | (j : ℝ) * L ≤ r y ∧ r y < ((j : ℝ) + 1) * L}
  have hAm (j : ℕ) : MeasurableSet (A j) :=
    (measurableSet_le measurable_const (continuous_distFrom g o).measurable).inter
      (measurableSet_lt (continuous_distFrom g o).measurable measurable_const)
  have hcover : (⋃ j, A j) = univ := by
    ext y
    simp only [mem_iUnion, mem_univ, iff_true]
    refine ⟨⌊r y / L⌋₊, ?_⟩
    exact ⟨(le_div_iff₀ hL).mp (Nat.floor_le (div_nonneg (g.induced_distance_nonneg o y) hL.le)),
      (div_lt_iff₀ hL).mp (Nat.lt_floor_add_one (r y / L))⟩
  have hpiece (j : ℕ) :
      (∫⁻ y in A j, ENNReal.ofReal (Real.exp (-(r y ^ 2) / (2 * L ^ 2))) ∂μ) ≤
        ENNReal.ofReal (gaussianVolumeTerm n j) * μ (distBall g.form o L) := by
    let e := Real.exp (-((j : ℝ) ^ 2) / 2)
    have he : 0 ≤ e := (Real.exp_pos _).le
    have hsub : A j ⊆ distBall g.form o (((j : ℝ) + 1) * L) := by
      intro y hy
      exact (mem_distBall_iff g o y (by positivity)).mpr hy.2
    have hBG := bishopGromov n M g hcomplete hK hRic μ hμ o L (((j : ℝ) + 1) * L)
      hL (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
    have hpoint (y : M.Carrier) (hy : y ∈ A j) :
        Real.exp (-(r y ^ 2) / (2 * L ^ 2)) ≤ e := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * L ^ 2) (by norm_num : (0 : ℝ) < 2)).mpr
      have h₁ := hy.1
      have h₂ : 0 ≤ (j : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL.le
      nlinarith [sq_nonneg (r y - (j : ℝ) * L),
        mul_nonneg (sub_nonneg.mpr h₁) (add_nonneg (g.induced_distance_nonneg o y) h₂)]
    calc
      _ ≤ ∫⁻ _ in A j, ENNReal.ofReal e ∂μ :=
        setLIntegral_mono' (hAm j) (fun y hy => ENNReal.ofReal_le_ofReal (hpoint y hy))
      _ = ENNReal.ofReal e * μ (A j) := by simp only [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal e * (ENNReal.ofReal (((((j : ℝ) + 1) * L) / L) ^ (2 * n)) *
          μ (distBall g.form o L)) := mul_le_mul_right ((measure_mono hsub).trans hBG) _
      _ = ENNReal.ofReal (gaussianVolumeTerm n j) * μ (distBall g.form o L) := by
        rw [mul_div_cancel_right₀ _ hL.ne', ← mul_assoc, ← ENNReal.ofReal_mul he]
        congr 1
        dsimp [gaussianVolumeTerm, e]
        ring
  calc
    _ = ∫⁻ y in ⋃ j, A j, ENNReal.ofReal (Real.exp (-(r y ^ 2) / (2 * L ^ 2))) ∂μ := by
      rw [hcover, Measure.restrict_univ]
    _ ≤ ∑' j, ∫⁻ y in A j, ENNReal.ofReal (Real.exp (-(r y ^ 2) / (2 * L ^ 2))) ∂μ :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' j, ENNReal.ofReal (gaussianVolumeTerm n j) * μ (distBall g.form o L) := ENNReal.tsum_le_tsum hpiece
    _ = ENNReal.ofReal (∑' j, gaussianVolumeTerm n j) * μ (distBall g.form o L) := by
      rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg
        (gaussianVolumeTerm_nonneg n) (gaussianVolumeTerm_summable n)]
    _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal (by
      dsimp [gaussianVolumeConstant]; linarith)) _

/-- The corresponding finite real Gaussian integral with a dimension-only constant. -/
theorem normalizedGaussianIntegral (g : SmoothMetric M) (hcomplete : IsComplete g)
    (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (L : ℝ) (hL : 0 < L) :
    (∫ y, Real.exp (-(distFrom g.form o y ^ 2) / (2 * L ^ 2)) ∂μ) ≤
      gaussianVolumeConstant n * (μ (distBall g.form o L)).toReal := by
  have hi : Integrable (fun y => Real.exp (-(distFrom g.form o y ^ 2) / (2 * L ^ 2))) μ := by
    convert integrable_exp_neg_distance_sq g hK hRic μ hμ o (a := 1 / (2 * L ^ 2)) (by positivity) using 1
    funext y
    congr 1
    dsimp [distFrom]
    ring
  have hh := normalizedGaussianLIntegral g hcomplete hK hRic μ hμ o L hL
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all μ (fun y => (Real.exp_pos _).le)),
    ← ENNReal.ofReal_toReal (riemannianVolume_distBall_lt_top g μ hμ o hL).ne,
    ← ENNReal.ofReal_mul (gaussianVolumeConstant_pos n).le] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (gaussianVolumeConstant_pos n).le ENNReal.toReal_nonneg)).mp hh

end Yau.NodeProofs.P08Aux.HeatMeasure
