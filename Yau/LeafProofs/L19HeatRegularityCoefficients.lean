import Yau.LeafProofs.L19HeatRegularityChartPairing

/-! The actual Kähler heat coefficients and the exact density drift identity. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual project heat coefficient is half the inverse physical real metric. -/
def scalarHeatChartCoeff (g : SmoothMetric M) (x : M.Carrier)
    (p : Parabolic.Point n) : Parabolic.Mat n :=
  fun i j => (1 / 2 : ℝ) * (realMetricFn g.form x p.1)⁻¹ i j

/-- Genuine joint smoothness of the computed heat coefficients. -/
theorem scalarHeatChartCoeff_smooth (g : SmoothMetric M) (x : M.Carrier)
    {O : Set (ComplexVector n)} (hOt : O ⊆ chartTarget x) (I : Set ℝ) :
    ParabolicCandidates.SmoothCoefficients (O ×ˢ I) (scalarHeatChartCoeff g x) (fun _ _ => 0) := by
  refine ⟨?_,fun _ => contDiffOn_const⟩
  classical
  have he (i j : RIdx n) : ContDiffOn ℝ ∞
      (fun p : Parabolic.Point n => ((1 / 2 : ℝ) * (realMetricFn g.form x p.1)⁻¹ i j) •
        (Matrix.single i j (1 : ℝ) : Parabolic.Mat n)) (O ×ˢ I) :=
    (contDiffOn_const.mul ((realMetricFn_inverse_contDiffOn g x i j).comp
      contDiffOn_fst (fun p hp => hOt hp.1))).smul contDiffOn_const
  have hs := ContDiffOn.sum (s := Finset.univ) (fun i _ =>
    ContDiffOn.sum (s := Finset.univ) (fun j _ => he i j))
  convert hs using 1
  funext p
  ext i j
  simp only [scalarHeatChartCoeff,Matrix.sum_apply,Matrix.smul_apply,Matrix.single_apply]
  simp only [ite_and]
  simp

/-- Coordinate differentiation of a quotient, proved using actual scalar
line derivatives rather than an assumed coordinate differentiation law. -/
theorem scalarChart_rDeriv_div {f k : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : DifferentiableAt ℝ f z) (hk : DifferentiableAt ℝ k z) (hkz : k z ≠ 0) (i : RIdx n) :
    rDeriv (fun w => f w / k w) z i =
      (rDeriv f z i * k z - f z * rDeriv k z i) / (k z)^2 := by
  have hfline : HasDerivAt (fun s : ℝ => f (z + s • realVec i)) (rDeriv f z i) 0 :=
    hf.hasFDerivAt.hasLineDerivAt (realVec i)
  have hkline : HasDerivAt (fun s : ℝ => k (z + s • realVec i)) (rDeriv k z i) 0 :=
    hk.hasFDerivAt.hasLineDerivAt (realVec i)
  have hqline : HasDerivAt (fun s : ℝ => f (z + s • realVec i) / k (z + s • realVec i))
      (rDeriv (fun w => f w / k w) z i) 0 :=
    (hf.mul (hk.inv hkz)).hasFDerivAt.hasLineDerivAt (realVec i)
  have hq := hfline.div hkline (by simpa using hkz)
  simpa only [zero_smul,add_zero] using hqline.unique hq

/-- The Kähler divergence identity gives exactly the drift correction
of the frozen nondivergence weak equation, with its required sign. -/
theorem scalarHeatChartCoeff_density_drift (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (t : ℝ) (j : RIdx n) :
    (∑ i, Parabolic.d (fun w => scalarHeatChartCoeff g x (w,t) i j) z i) =
      -(∑ i, scalarHeatChartCoeff g x (z,t) i j *
        rDeriv (fun w => Real.sqrt (realMetricFn g.form x w).det) z i /
          Real.sqrt (realMetricFn g.form x z).det) := by
  let ρ := fun w => Real.sqrt (realMetricFn g.form x w).det
  let A := fun w => (realMetricFn g.form x w)⁻¹
  have hρ : DifferentiableAt ℝ ρ z :=
    ((volumeDensity_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hA (i) : DifferentiableAt ℝ (fun w => A w i j) z :=
    ((realMetricFn_inverse_contDiffOn g x i j).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hρz : ρ z ≠ 0 := ne_of_gt (L12Aux.volumeDensity_pos g.form x z hz)
  have hdiv := kahler_density_inverse_divergence_on g hK x hz j
  have hdiv' : (∑ i, rDeriv ρ z i * A z i j) +
      ρ z * ∑ i, rDeriv (fun w => A w i j) z i = 0 := by
    have he (i : RIdx n) : rDeriv (fun w => ρ w * A w i j) z i =
        rDeriv ρ z i * A z i j + ρ z * rDeriv (fun w => A w i j) z i :=
      rDeriv_mul hρ (hA i) i
    change (∑ i, rDeriv (fun w => ρ w * A w i j) z i) = 0 at hdiv
    simp_rw [he] at hdiv
    simpa only [Finset.sum_add_distrib,Finset.mul_sum] using hdiv
  have ha : (∑ i, Parabolic.d (fun w => scalarHeatChartCoeff g x (w,t) i j) z i) =
      (1 / 2 : ℝ) * ∑ i, rDeriv (fun w => A w i j) z i := by
    change (∑ i, rDeriv (fun w => (1 / 2 : ℝ) * A w i j) z i) = _
    simp_rw [rDeriv_const_mul (hA _)]; rw [Finset.mul_sum]
  have hb : (∑ i, scalarHeatChartCoeff g x (z,t) i j * rDeriv ρ z i / ρ z) =
      ((1 / 2 : ℝ) / ρ z) * ∑ i, rDeriv ρ z i * A z i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [scalarHeatChartCoeff,A]
    ring
  rw [ha,hb]
  apply (mul_left_injective₀ hρz)
  field_simp
  nlinarith only [hdiv']

/-- The density-corrected chart energy is exactly the spatial part of
the frozen weak nondivergence equation. -/
theorem scalarHeatChartCoeff_density_test (g : SmoothMetric M) (hK : IsKahler g) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (t : ℝ)
    {φ : ComplexVector n → ℝ} (hφ : DifferentiableAt ℝ φ z) (G : RIdx n → ℝ) :
    Real.sqrt (realMetricFn g.form x z).det *
      (∑ i, ∑ j, scalarHeatChartCoeff g x (z,t) i j * G j *
        rDeriv (fun w => φ w / Real.sqrt (realMetricFn g.form x w).det) z i) =
      (∑ i, ∑ j, scalarHeatChartCoeff g x (z,t) i j * G j * rDeriv φ z i) +
      ∑ j, (∑ i, Parabolic.d (fun w => scalarHeatChartCoeff g x (w,t) i j) z i) * G j * φ z := by
  let ρ := fun w => Real.sqrt (realMetricFn g.form x w).det
  let a := scalarHeatChartCoeff g x (z,t)
  have hρ : DifferentiableAt ℝ ρ z :=
    ((volumeDensity_contDiffOn g x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  have hρz : ρ z ≠ 0 := ne_of_gt (L12Aux.volumeDensity_pos g.form x z hz)
  have hterm (i j : RIdx n) : ρ z * (a i j * G j *
      rDeriv (fun w => φ w / ρ w) z i) =
      a i j * G j * rDeriv φ z i - (a i j * rDeriv ρ z i / ρ z) * G j * φ z := by
    rw [scalarChart_rDeriv_div hφ hρ hρz]
    field_simp
  have hexpand : ρ z * (∑ i, ∑ j, a i j * G j * rDeriv (fun w => φ w / ρ w) z i) =
      (∑ i, ∑ j, a i j * G j * rDeriv φ z i) -
        ∑ j, (∑ i, a i j * rDeriv ρ z i / ρ z) * G j * φ z := by
    simp only [Finset.mul_sum]
    simp_rw [hterm]
    simp only [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Finset.sum_mul]
  change ρ z * (∑ i, ∑ j, a i j * G j * rDeriv (fun w => φ w / ρ w) z i) = _
  rw [hexpand]
  simp_rw [scalarHeatChartCoeff_density_drift g hK x hz t]
  simp only [neg_mul,Finset.sum_neg_distrib]
  ring

end Yau.LeafProofs.L19Aux
