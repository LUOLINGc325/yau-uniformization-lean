import Yau.Proofs.F02InitialRicci
import Yau.Proofs.F03WeightBasic
import Yau.LeafProofs.L19GaussianIntegrability
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Polynomial integrability of the actual controlled exhaustion. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Manifold ENNReal ContDiff InnerProductSpace ComplexOrder

namespace Yau.Proofs.F03Aux
open Yau Blueprint
open LeafProofs.L12Aux LeafProofs.L18Aux LeafProofs.L19Aux

variable {n : ℕ}

theorem controlledExhaustion_polynomial_integrable
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) (μ : Measure (Pt X))
    (hμ : IsRiemannianVolume X.metric.form μ) (k : ℕ) (hk : 2 * n < k) :
    (∫⁻ x, ENNReal.ofReal ((u x) ^ (-(k : ℤ))) ∂μ) < ⊤ := by
  let g := X.metric
  let := underlyingRealTangentNormedAddCommGroup g.form o
  let := underlyingRealTangentInnerProductSpace g.form o
  let : MeasurableSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := borel _
  let : BorelSpace (TangentSpace 𝓘(ℝ, ComplexVector n) o) := ⟨rfl⟩
  have : (realTangentVolume g o).IsAddHaarMeasure := realTangentVolume_isAddHaarMeasure g o
  obtain ⟨C, hC, hub⟩ := hu.2.2.2
  have hu0 (x : Pt X) : 0 < u x := zero_lt_one.trans_le (hu.2.2.1 x)
  have hφ : Continuous (fun x => (u x) ^ (-(k : ℤ))) := by
    simp only [zpow_neg, zpow_natCast]
    exact ((continuous_of_smoothFn hu.1).pow k).inv₀ (fun x => pow_ne_zero _ (hu0 x).ne')
  have hmeas : Measurable (fun x => ENNReal.ofReal ((u x) ^ (-(k : ℤ)))) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) o) = 2 * n := by
    simpa only [Fintype.card_fin] using
      Module.finrank_eq_card_basis (realInitialOrthonormalFrame g o).toBasis
  have hpoly : Integrable
      (fun v : TangentSpace 𝓘(ℝ, ComplexVector n) o => (1 + ‖v‖) ^ (-(k : ℝ)))
      (realTangentVolume g o) := by
    apply integrable_one_add_norm
    rw [hdim]
    exact_mod_cast hk
  let D := realStrictMinimizingVectors g o
  let E := realExponentialMap g o
  let ν := ((realTangentVolume g o).withDensity
    (fun v => ENNReal.ofReal (realExponentialVolumeDensity g o v))).restrict D
  have hpoint (v : TangentSpace 𝓘(ℝ, ComplexVector n) o) (hv : v ∈ D) :
      (u (E v)) ^ (-(k : ℤ)) ≤ C ^ k * (1 + ‖v‖) ^ (-(k : ℝ)) := by
    have hmin := realStrictMinimizingVectors_subset g o hv
    change distFrom g.form o (E v) = ‖v‖ at hmin
    have hlo := (hub (E v)).1
    rw [hmin] at hlo
    have hbase : 0 < C⁻¹ * (1 + ‖v‖) := by positivity
    have hinv : (u (E v) ^ k)⁻¹ ≤ ((C⁻¹ * (1 + ‖v‖)) ^ k)⁻¹ :=
      (inv_le_inv₀ (pow_pos (hu0 _) _) (pow_pos hbase _)).mpr
        (pow_le_pow_left₀ hbase.le hlo _)
    calc
      (u (E v)) ^ (-(k : ℤ)) = (u (E v) ^ k)⁻¹ := by simp
      _ ≤ ((C⁻¹ * (1 + ‖v‖)) ^ k)⁻¹ := hinv
      _ = C ^ k * (1 + ‖v‖) ^ (-(k : ℝ)) := by
        rw [mul_pow, mul_inv, inv_pow, inv_inv, Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hbound : (∫⁻ x, ENNReal.ofReal ((u x) ^ (-(k : ℤ))) ∂μ) ≤
      ENNReal.ofReal (C ^ k) * ∫⁻ v : TangentSpace 𝓘(ℝ, ComplexVector n) o,
        ENNReal.ofReal ((1 + ‖v‖) ^ (-(k : ℝ))) ∂realTangentVolume g o := by
    rw [realExponential_strictMinimizing_measure_transport g o μ hμ,
      lintegral_map hmeas (realExponentialMap_contMDiff g o).continuous.measurable]
    change (∫⁻ v in D, ENNReal.ofReal ((u (E v)) ^ (-(k : ℤ)))
      ∂(realTangentVolume g o).withDensity _) ≤ _
    calc
      _ ≤ ∫⁻ v in D, ENNReal.ofReal (C ^ k * (1 + ‖v‖) ^ (-(k : ℝ)))
          ∂(realTangentVolume g o).withDensity _ :=
        setLIntegral_mono' (measurableSet_realStrictMinimizingVectors g o)
          (fun v hv => ENNReal.ofReal_le_ofReal (hpoint v hv))
      _ ≤ ∫⁻ v : TangentSpace 𝓘(ℝ, ComplexVector n) o,
          ENNReal.ofReal (C ^ k * (1 + ‖v‖) ^ (-(k : ℝ))) ∂realTangentVolume g o :=
        lintegral_mono' (strictExponentialDensity_measure_le g X.kahler_metric
          (F02Aux.initialRicci_posSemidef X o h U P ρ hf) o) le_rfl
      _ = _ := by
        simp_rw [ENNReal.ofReal_mul (pow_nonneg hC.le _)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun v => Real.rpow_nonneg (by positivity) _))).mp hpoly.2))

/-- One threshold is selected before every k and every genuine volume. -/
theorem controlledExhaustion_polynomial_threshold
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ μ, IsRiemannianVolume X.metric.form μ →
      (∫⁻ x, ENNReal.ofReal ((u x) ^ (-(k : ℤ))) ∂μ) < ⊤ := by
  refine ⟨2 * n + 1, fun k hk μ hμ => ?_⟩
  exact controlledExhaustion_polynomial_integrable X o h U P ρ hf u hu μ hμ k (by omega)

/-- Actual exponential weights inherit the proved polynomial integrability.
Only the intermediate correction size estimate is used here. -/
theorem comparisonWeight_integrable_of_size
    (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) (H : STF X) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (k : ℕ) (hk : 2 * n < k)
    (t : ℝ) (hH : ∀ x, |H x t| ≤ B * (u x) ^ 2)
    (μ : Measure (Pt X)) (hμ : IsRiemannianVolume X.metric.form μ) :
    (∫⁻ x, ENNReal.ofReal (comparisonWeight u H A k x t) ∂μ) < ⊤ := by
  have hi := controlledExhaustion_polynomial_integrable X o h U P ρ hf u hu μ hμ k hk
  have hb : (∫⁻ x, ENNReal.ofReal (comparisonWeight u H A k x t) ∂μ) ≤
      ENNReal.ofReal (Real.exp (A * B)) *
        (∫⁻ x, ENNReal.ofReal ((u x) ^ (-(k : ℤ))) ∂μ) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (A * B) * (u x) ^ (-(k : ℤ))) ∂μ :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal
          ((comparisonWeight_bounds u H hA hB k x t
            (zero_lt_one.trans_le (hu.2.2.1 x)) (hH x)).2))
      _ = _ := by
        simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact hb.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hi)

end Yau.Proofs.F03Aux
