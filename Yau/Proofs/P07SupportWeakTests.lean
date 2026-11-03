import Yau.Proofs.P07SupportWeakRegularization
import Yau.Proofs.P07DistanceLeviTests
import Yau.Proofs.P06WeakLeviSmooth

/-! The literal compact-test inequality, with both true integrability conclusions. -/
noncomputable section
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
namespace Yau.NodeProofs.P07Aux.SupportWeak
open Yau Yau.Blueprint Yau.LeafProofs L18Aux L22Aux P06Aux P07DistanceLevi
variable {n : ℕ}

/-- Compact smooth tests transfer a local upper support bound to the actual current. -/
theorem compactTest_upper_of_localUpperSupports
    {O : Set (ComplexVector n)} {f h : ComplexVector n → ℝ} {v : ComplexVector n}
    (hO : IsOpen O) (hf : ContinuousOn f O) (hh : ContinuousOn h O)
    (hs : LocalDirectionalUpperSupportsOn O f h v)
    {φ : ComplexVector n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) (hφpos : ∀ z, 0 ≤ φ z) :
    Integrable (fun z => f z * leviDirection (leviC φ z) v) (lebesgueC n) ∧
    Integrable (fun z => φ z * h z) (lebesgueC n) ∧
    (∫ z, f z * leviDirection (leviC φ z) v ∂lebesgueC n) ≤
      ∫ z, φ z * h z ∂lebesgueC n := by
  letI : IsLocallyFiniteMeasure (lebesgueC n) := by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    infer_instance
  let Dφ : ComplexVector n → ℝ := fun z => leviDirection (leviC φ z) v
  have hDc : Continuous Dφ := continuous_leviDirection_test hφ v
  have hDcpt : HasCompactSupport Dφ := hasCompactSupport_leviDirection_test hφ hcφ v
  have hDO : tsupport Dφ ⊆ O := (tsupport_leviDirection_test_subset hφ v).trans hφO
  have hiD : Integrable Dφ (lebesgueC n) := hDc.integrable_of_hasCompactSupport hDcpt
  have hiAbs : Integrable (fun z => |Dφ z|) (lebesgueC n) := hiD.norm
  have hiφ : Integrable φ (lebesgueC n) := hφ.continuous.integrable_of_hasCompactSupport hcφ
  have hif : Integrable (fun z => f z * Dφ z) (lebesgueC n) := by
    simpa only [mul_comm] using integrable_compactTest_mul (lebesgueC n) hO hDc hDcpt hDO hf
  have hih : Integrable (fun z => φ z * h z) (lebesgueC n) :=
    integrable_compactTest_mul (lebesgueC n) hO hφ.continuous hcφ hφO hh
  refine ⟨hif, hih, ?_⟩
  let A : ℝ := ∫ z, |Dφ z| ∂lebesgueC n
  let B : ℝ := ∫ z, φ z ∂lebesgueC n
  have hA : 0 ≤ A := integral_nonneg (fun z => abs_nonneg _)
  have hB : 0 ≤ B := integral_nonneg hφpos
  have happrox : ∀ η : ℝ, 0 < η →
      (∫ z, f z * Dφ z ∂lebesgueC n) ≤ (∫ z, φ z * h z ∂lebesgueC n) + η * (A + B) := by
    intro η hη
    obtain ⟨u, hu, huf, huh⟩ := exists_smooth_directionalUpper_approx_on_compact
      hO hf hh hs hcφ hφO hη hη
    have hiu : Integrable (fun z => u z * Dφ z) (lebesgueC n) := by
      simpa only [mul_comm] using integrable_compactTest_mul (lebesgueC n) hO
        hDc hDcpt hDO hu.continuous.continuousOn
    have hiφDu : Integrable (fun z => φ z * leviDirection (leviC u z) v) (lebesgueC n) :=
      integrable_compactTest_mul (lebesgueC n) hO hφ.continuous hcφ hφO
        (leviDirection_contDiffOn hO hu.contDiffOn v).continuousOn
    have hiφhη : Integrable (fun z => φ z * (h z + η)) (lebesgueC n) :=
      integrable_compactTest_mul (lebesgueC n) hO hφ.continuous hcφ hφO
        (hh.add continuousOn_const)
    have hleft : (∫ z, f z * Dφ z ∂lebesgueC n) ≤
        (∫ z, u z * Dφ z ∂lebesgueC n) + η * A := by
      rw [← integral_const_mul, ← integral_add hiu (hiAbs.const_mul η)]
      apply integral_mono hif (hiu.add (hiAbs.const_mul η))
      intro z
      change f z * Dφ z ≤ u z * Dφ z + η * |Dφ z|
      by_cases hz : z ∈ tsupport φ
      · have hfuz : |f z - u z| ≤ η := by simpa only [abs_sub_comm] using huf z hz
        have hm := mul_le_mul_of_nonneg_right hfuz (abs_nonneg (Dφ z))
        have ha := le_abs_self ((f z - u z) * Dφ z)
        rw [abs_mul] at ha
        nlinarith
      · have hzero : Dφ z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_leviDirection_test_subset hφ v h))
        simp only [hzero, mul_zero, abs_zero, add_zero, le_refl]
    have hright : (∫ z, φ z * leviDirection (leviC u z) v ∂lebesgueC n) ≤
        ∫ z, φ z * (h z + η) ∂lebesgueC n := by
      apply integral_mono hiφDu hiφhη
      intro z
      by_cases hz : z ∈ tsupport φ
      · exact mul_le_mul_of_nonneg_left (huh z hz) (hφpos z)
      · have hzero : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp only [hzero, zero_mul, le_refl]
    have hparts := integral_leviDirection_test hO hφ hcφ hφO hu.contDiffOn v
    change (∫ z, u z * Dφ z ∂lebesgueC n) = _ at hparts
    rw [hparts] at hleft
    have heq : (∫ z, φ z * (h z + η) ∂lebesgueC n) =
        (∫ z, φ z * h z ∂lebesgueC n) + η * B := by
      simp_rw [mul_add]
      rw [integral_add hih (hiφ.mul_const η), integral_mul_const]
      dsimp [B]
      ring
    rw [heq] at hright
    linarith
  by_contra hn
  let d : ℝ := (∫ z, f z * Dφ z ∂lebesgueC n) - ∫ z, φ z * h z ∂lebesgueC n
  have hd : 0 < d := sub_pos.mpr (lt_of_not_ge hn)
  have hden : 0 < 2 * (A + B + 1) := by linarith
  have hm := happrox (d / (2 * (A + B + 1))) (div_pos hd hden)
  have hcancel : d / (2 * (A + B + 1)) * (2 * (A + B + 1)) = d := div_mul_cancel₀ _ hden.ne'
  dsimp [d] at hd hm hcancel
  nlinarith

/-- The original chart quantifiers and the unscaled second integrability clause are retained. -/
theorem weakLeviUpper_of_localUpperSupports
    {M : ComplexManifold n} (g : SmoothMetric M) {f : M.Carrier → ℝ}
    (hf : Continuous f) (C : ℝ)
    (hs : ∀ (x : M.Carrier) (z : ComplexVector n), z ∈ chartTarget x →
      ∃ S : ComplexVector n → ℝ, ContDiffAt ℝ 2 S z ∧
        S z = inChart x f z ∧ (∀ᶠ w in 𝓝 z, inChart x f w ≤ S w) ∧
        ∀ v, leviDirection (leviC S z) v ≤ C * leviDirection (hMat g.form x z) v) :
    WeakLeviUpper g.form f C := by
  intro x v φ hφ hcφ hφO hφpos
  have hO : IsOpen (chartTarget x) := isOpen_extChartAt_target (I := ComplexModel n) x
  have hfc : ContinuousOn (inChart x f) (chartTarget x) :=
    hf.comp_continuousOn (continuousOn_extChartAt_symm (I := ComplexModel n) x)
  have hmetric := (metricLeviDirection_contDiffOn g x v).continuousOn
  have hscaled : ContinuousOn (fun z => C * leviDirection (hMat g.form x z) v) (chartTarget x) :=
    continuousOn_const.mul hmetric
  have hsupport : LocalDirectionalUpperSupportsOn (chartTarget x) (inChart x f)
      (fun z => C * leviDirection (hMat g.form x z) v) v := by
    intro z hz
    obtain ⟨S, hS, hSz, hSf, hSv⟩ := hs x z hz
    exact ⟨S, hS, hSz, hSf, hSv v⟩
  obtain ⟨hiL, _, hle⟩ := compactTest_upper_of_localUpperSupports hO hfc hscaled
    hsupport hφ hcφ hφO hφpos
  have hiR := (compactTest_integrability hO hfc v hmetric hφ hcφ hφO).2
  refine ⟨hiL, hiR, ?_⟩
  have heq : (fun z => φ z * (C * leviDirection (hMat g.form x z) v)) =
      (fun z => C * (φ z * leviDirection (hMat g.form x z) v)) := by
    funext z
    ring
  rw [heq, integral_const_mul] at hle
  exact hle

end Yau.NodeProofs.P07Aux.SupportWeak
