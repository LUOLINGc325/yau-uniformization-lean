import Yau.LeafProofs.L17CutoffJetHolder
import Yau.LeafProofs.L17FrozenResidualHolder
import Yau.LeafProofs.L17LocalizedGaussianBounds

/-! The true unit-coordinate Gaussian residual and its quantitative Holder estimate. -/

open Set Metric
open scoped Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SourceLocalizationAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def cutoffHolderBudget (B : ℕ → ℝ) (γ : ℝ) (k : ℕ) : ℝ :=
  B k + B (k+1) * (4 : ℝ)^(1-γ)

def unitGaussianResidual (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) : Point n → ℝ :=
  scalarFrozenResidual (fun q => chartCoefficient P.charts p (P.radius • q.1))
    (fun q => chartCoefficient P.charts p 0 - chartCoefficient P.charts p (P.radius • q.1))
    (fun z => P.localization p (P.charts.chart p (P.radius • z)))
    (P.charts.frozenHeatDuhamel p (rescaledSource P T hT f p))

theorem unitGaussianResidual_holderBound (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (hRadius : 2*P.radius < P.charts.radius) {γ C J : ℝ} (hγ : γ ≤ 1)
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (f : HolderSpace P T γ) (p : P.centers)
    (hχ : ∀ k z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
      ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart p w)) z‖ ≤ B k*(P.radius⁻¹)^k)
    (hSchauder : SchauderBound γ (cylinder Set.univ 0 (T/P.radius^2))
      (P.charts.frozenHeatDuhamel p (rescaledSource P T hT f p)) C)
    (hJet : HolderBound γ (cylinder Set.univ 0 (T/P.radius^2))
      (fun q => (P.charts.frozenHeatDuhamel p (rescaledSource P T hT f p) q,
        spatialD (P.charts.frozenHeatDuhamel p (rescaledSource P T hT f p)) q)) J) :
    let b := coefficientBudget P.charts
    let r := (4 : ℝ)^(1-γ)
    HolderBound γ (cylinder (ball (0 : Space n) 2) 0 (T/P.radius^2))
      (unitGaussianResidual P T hT f p)
      ((Fintype.card (RIdx n) : ℝ)^2 *
        (4*cutoffHolderBudget B γ 0*(b*P.radius*(2+r))*C +
          8*(b+b*P.radius*r)*cutoffHolderBudget B γ 1*J +
          4*(b+b*P.radius*r)*cutoffHolderBudget B γ 2*J)) := by
  obtain ⟨hχ0,hχ1,hχ2⟩ := scaled_backgroundChart_three_jet_holderBounds P.charts
    (P.localization_smooth p) P.radius_pos hRadius p B hB hχ (T/P.radius^2) γ hγ
  have ha := scaled_chartCoefficient_holderBound (T := T/P.radius^2) P.charts P.radius_pos hRadius hγ p
  have hd := scaled_frozenCoefficient_holderBound (T := T/P.radius^2) P.charts P.radius_pos hRadius hγ p
  have hd' : HolderBound γ (cylinder (ball (0 : Space n) 2) 0 (T/P.radius^2))
      (fun q => chartCoefficient P.charts p 0-chartCoefficient P.charts p (P.radius • q.1))
      (coefficientBudget P.charts*P.radius*(2+(4 : ℝ)^(1-γ))) := by
    convert hd using 1
    ring
  have hSub : cylinder (ball (0 : Space n) 2) 0 (T/P.radius^2) ⊆ cylinder Set.univ 0 (T/P.radius^2) :=
    fun _ hq => ⟨mem_univ _,hq.2⟩
  have h := scalarFrozenResidual_holderBound (fun i j => holderBound_matrix_entry_max ha i j)
    (fun i j => holderBound_matrix_entry_max hd' i j) hχ0 hχ1 hχ2
    (L16Aux.holderBound_mono hJet hSub) (L16Aux.holderBound_mono hSchauder.2.2.2.1 hSub)
  simpa only [unitGaussianResidual,cutoffHolderBudget] using h

theorem cutoffHolderBudget_nonneg (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (γ : ℝ) (k : ℕ) :
    0 ≤ cutoffHolderBudget B γ k := by
  exact add_nonneg (hB k) (mul_nonneg (hB (k+1)) (Real.rpow_nonneg (by norm_num) _))

def unitGaussianResidualBudget (A : BoundedChartFamily g) (B : ℕ → ℝ) (γ K : ℝ) : ℝ :=
  let b := coefficientBudget A
  let r := (4 : ℝ)^(1-γ)
  1 + (Fintype.card (RIdx n) : ℝ)^2 * K *
    (4*cutoffHolderBudget B γ 0*b*(2+r) +
      8*(b*(1+r))*cutoffHolderBudget B γ 1 + 4*(b*(1+r))*cutoffHolderBudget B γ 2)

theorem unitGaussianResidualBudget_pos (A : BoundedChartFamily g) (B : ℕ → ℝ)
    (hB : ∀ k, 0 ≤ B k) (γ : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    0 < unitGaussianResidualBudget A B γ K := by
  have hb : 0 ≤ coefficientBudget A := zero_le_one.trans (coefficientBudget_ge_one A)
  have h0 := cutoffHolderBudget_nonneg B hB γ 0
  have h1 := cutoffHolderBudget_nonneg B hB γ 1
  have h2 := cutoffHolderBudget_nonneg B hB γ 2
  dsimp only [unitGaussianResidualBudget]
  positivity

theorem unitGaussianResidual_small_bound (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    (hRadius : 2*P.radius < P.charts.radius) (hr : P.radius ≤ 1)
    {γ K s : ℝ} (hγ : γ ≤ 1) (hK : 0 ≤ K) (hs : 0 ≤ s)
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k) (f : HolderSpace P T γ) (p : P.centers)
    (hχ : ∀ k z, z ∈ ball (0 : ComplexVector n) (2*P.radius) →
      ‖iteratedFDeriv ℝ k (fun w => P.localization p (P.charts.chart p w)) z‖ ≤ B k*(P.radius⁻¹)^k)
    (hSchauder : SchauderBound γ (cylinder Set.univ 0 (T/P.radius^2))
      (P.charts.frozenHeatDuhamel p (rescaledSource P T hT f p)) (K*‖f‖))
    (hJet : HolderBound γ (cylinder Set.univ 0 (T/P.radius^2))
      (fun q => (P.charts.frozenHeatDuhamel p (rescaledSource P T hT f p) q,
        spatialD (P.charts.frozenHeatDuhamel p (rescaledSource P T hT f p)) q)) (K*‖f‖*s)) :
    HolderBound γ (cylinder (ball (0 : Space n) 2) 0 (T/P.radius^2))
      (unitGaussianResidual P T hT f p)
      (unitGaussianResidualBudget P.charts B γ K * ‖f‖ * (P.radius+s)) := by
  have h := unitGaussianResidual_holderBound P T hT hRadius hγ B hB f p hχ hSchauder hJet
  apply L16Aux.holderBound_mono_const h
  let b := coefficientBudget P.charts
  let r := (4 : ℝ)^(1-γ)
  let E0 := cutoffHolderBudget B γ 0
  let E1 := cutoffHolderBudget B γ 1
  let E2 := cutoffHolderBudget B γ 2
  let A := 4*E0*b*(2+r)
  let D := 8*(b*(1+r))*E1+4*(b*(1+r))*E2
  have hb : 0 ≤ b := zero_le_one.trans (coefficientBudget_ge_one P.charts)
  have hpow : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have h0 : 0 ≤ E0 := cutoffHolderBudget_nonneg B hB γ 0
  have h1 : 0 ≤ E1 := cutoffHolderBudget_nonneg B hB γ 1
  have h2 : 0 ≤ E2 := cutoffHolderBudget_nonneg B hB γ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hM : b+b*P.radius*r ≤ b*(1+r) := by
    nlinarith [mul_nonneg (mul_nonneg hb hpow) (sub_nonneg.mpr hr)]
  have hLower : 8*(b+b*P.radius*r)*E1+4*(b+b*P.radius*r)*E2 ≤ D := by
    dsimp only [D]
    gcongr
  have hMain : A*P.radius+D*s ≤ (A+D)*(P.radius+s) := by
    nlinarith [mul_nonneg hA hs,mul_nonneg hD P.radius_pos.le]
  have hρs : 0 ≤ P.radius+s := add_nonneg P.radius_pos.le hs
  calc
    _ = (Fintype.card (RIdx n) : ℝ)^2*(K*‖f‖)*
        (A*P.radius+(8*(b+b*P.radius*r)*E1+4*(b+b*P.radius*r)*E2)*s) := by
      dsimp only [A,b,r,E0,E1,E2]
      ring
    _ ≤ (Fintype.card (RIdx n) : ℝ)^2*(K*‖f‖)*(A*P.radius+D*s) := by gcongr
    _ ≤ (Fintype.card (RIdx n) : ℝ)^2*(K*‖f‖)*((A+D)*(P.radius+s)) :=
      mul_le_mul_of_nonneg_left hMain (mul_nonneg (sq_nonneg _) (mul_nonneg hK (norm_nonneg f)))
    _ = (unitGaussianResidualBudget P.charts B γ K-1)*‖f‖*(P.radius+s) := by
      dsimp only [unitGaussianResidualBudget,A,D,b,r,E0,E1,E2]
      ring
    _ ≤ _ := by gcongr; linarith

end Yau.LeafProofs.L17Aux
