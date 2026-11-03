import Yau.Proofs.D02RemovableRegularity
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Polar Tonelli for the actual ordinary planar area used by D02.
All radial energies are nonnegative extended integrals, so no boundary
extension or integrability assumption is needed in the change of variables. -/

open scoped ENNReal Manifold Topology ContDiff
open MeasureTheory Set

noncomputable section
namespace Yau.NodeProofs.D02RemovableAux

def polarPoint (r θ : ℝ) : ℂ := Complex.polarCoord.symm (r, θ)

theorem polarPoint_norm (r θ : ℝ) : ‖polarPoint r θ‖ = |r| :=
  Complex.norm_polarCoord_symm (r, θ)

theorem polarPoint_continuous : Continuous (fun p : ℝ × ℝ => polarPoint p.1 p.2) := by
  simp only [polarPoint, Complex.polarCoord_symm_apply]
  fun_prop

/-- Exact polar integration of a measurable density on a genuine annulus. -/
theorem annulus_lintegral_polar_nonneg (Q : ℂ → ℝ≥0∞) (hQ : Measurable Q)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    (∫⁻ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, Q z) =
      ∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioo a b,
        ENNReal.ofReal r * Q (polarPoint r θ) := by
  let A : Set ℂ := {z | a < ‖z‖ ∧ ‖z‖ < b}
  let D : Set (ℝ × ℝ) := Ioo a b ×ˢ Ioo (-Real.pi) Real.pi
  let G : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * Q (polarPoint p.1 p.2)
  have hA : MeasurableSet A :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      (hQ.comp polarPoint_continuous.measurable)
  have hchange : (∫⁻ z in A, Q z) = ∫⁻ p in D, G p := by
    rw [← lintegral_indicator hA, ← Complex.lintegral_comp_polarCoord_symm]
    change (∫⁻ p in polarCoord.target,
      ENNReal.ofReal p.1 * A.indicator Q (Complex.polarCoord.symm p)) = ∫⁻ p in D, G p
    have hT : MeasurableSet polarCoord.target := measurableSet_Ioi.prod measurableSet_Ioo
    have hD : MeasurableSet D := measurableSet_Ioo.prod measurableSet_Ioo
    rw [← lintegral_indicator hT, ← lintegral_indicator hD]
    apply lintegral_congr
    intro p
    by_cases hpD : p ∈ D
    · have hpT : p ∈ polarCoord.target := ⟨ha.trans_lt hpD.1.1, hpD.2⟩
      have hpA : Complex.polarCoord.symm p ∈ A := by
        change a < ‖Complex.polarCoord.symm p‖ ∧ ‖Complex.polarCoord.symm p‖ < b
        rw [Complex.norm_polarCoord_symm, abs_of_pos (ha.trans_lt hpD.1.1)]
        exact hpD.1
      rw [indicator_of_mem hpT, indicator_of_mem hpD, indicator_of_mem hpA]
      rfl
    · by_cases hpT : p ∈ polarCoord.target
      · have hpA : Complex.polarCoord.symm p ∉ A := by
          intro hpA
          apply hpD
          refine ⟨?_, hpT.2⟩
          change a < p.1 ∧ p.1 < b
          simpa only [A, mem_ofPred_eq, Complex.norm_polarCoord_symm,
            abs_of_pos (show 0 < p.1 from hpT.1)] using hpA
        rw [indicator_of_mem hpT, indicator_of_notMem hpD,
          indicator_of_notMem hpA, mul_zero]
      · rw [indicator_of_notMem hpT, indicator_of_notMem hpD]
  rw [hchange, Measure.volume_eq_prod]
  exact setLIntegral_prod_symm G hG.aemeasurable


open Yau Yau.Blueprint Yau.NodeProofs.D02Aux

/-- The polar parametrization used for area is the same genuine ray used
for the radial limit. -/
theorem polarPoint_eq_exp (r θ : ℝ) :
    polarPoint r θ = (r : ℂ) * Complex.exp (θ * Complex.I) := by
  simp [polarPoint, Complex.polarCoord_symm_apply, Complex.exp_ofReal_mul_I]

/-- Polar Tonelli supplies one actual ray with finite weighted physical
energy, directly from the original D03 weighted integral. -/
theorem exists_good_physical_ray {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) {f : ℂ → M.Carrier}
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f puncturedUnitDisc)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hσ : 0 < σ)
    (henergy : physicalWeightedEnergy g.form f ρ σ < ⊤) :
    ∃ θ : ℝ, IntegrableOn
      (fun r ↦ hermitianNormSq (g.form (f (polarPoint r θ)))
        (physicalCurveDerivative f (polarPoint r θ)) * r ^ (1 - σ)) (Ioo 0 ρ) volume := by
  classical
  let A := {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ}
  let q := fun z ↦ hermitianNormSq (g.form (f z)) (physicalCurveDerivative f z)
  have hA : IsOpen A := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hAunit : A ⊆ puncturedUnitDisc := fun z hz ↦ ⟨hz.1, hz.2.trans hρ1⟩
  have hqc : ContinuousOn q A := (physicalEnergy_continuousOn g hf).mono hAunit
  have hweight : ContinuousOn (fun z : ℂ ↦ ‖z‖ ^ (-σ)) A :=
    continuous_norm.continuousOn.rpow_const (fun z hz ↦ Or.inl hz.1.ne')
  let Q := A.indicator (fun z ↦ ENNReal.ofReal (q z * ‖z‖ ^ (-σ)))
  have hQc : ContinuousOn (fun z ↦ ENNReal.ofReal (q z * ‖z‖ ^ (-σ))) A :=
    ENNReal.continuous_ofReal.comp_continuousOn (hqc.mul hweight)
  have hQ : Measurable Q := by
    have heqQ : Q = A.piecewise (fun z ↦ ENNReal.ofReal (q z * ‖z‖ ^ (-σ))) (fun _ ↦ 0) := by
      funext z
      by_cases hz : z ∈ A <;> simp [Q, hz]
    rw [heqQ]
    exact hQc.measurable_piecewise
      (continuousOn_const : ContinuousOn (fun _ : ℂ ↦ (0 : ℝ≥0∞)) Aᶜ) hA.measurableSet
  have hE : (∫⁻ z in A, Q z) < ⊤ := by
    convert henergy using 1
    apply setLIntegral_congr_fun hA.measurableSet
    intro z hz
    exact indicator_of_mem hz _
  have hpolar := annulus_lintegral_polar_nonneg Q hQ (a := 0) (b := ρ) le_rfl hρ
  have htotal : (∫⁻ θ in Ioo (-Real.pi) Real.pi, ∫⁻ r in Ioo 0 ρ,
      ENNReal.ofReal r * Q (polarPoint r θ)) < ⊤ := by
    rw [← hpolar]
    exact hE
  have hθmeas : Measurable (fun θ ↦ ∫⁻ r in Ioo 0 ρ, ENNReal.ofReal r * Q (polarPoint r θ)) := by
    have hm : Measurable (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 * Q (polarPoint p.1 p.2)) :=
      (ENNReal.measurable_ofReal.comp measurable_fst).mul (hQ.comp polarPoint_continuous.measurable)
    exact Measurable.lintegral_prod_left' (μ := volume.restrict (Ioo 0 ρ)) hm
  have hnonzero : (volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi) ≠ 0 := by
    intro hz
    have heq := congrArg (fun ν : Measure ℝ ↦ ν univ) hz
    have hpos : (0 : ENNReal) < volume (Ioo (-Real.pi) Real.pi) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
    simp only [Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] at heq
    exact hpos.ne' heq
  letI : NeZero ((volume : Measure ℝ).restrict (Ioo (-Real.pi) Real.pi)) := ⟨hnonzero⟩
  obtain ⟨θ, hθ, hfinite⟩ := ((ae_restrict_mem measurableSet_Ioo).and
    (ae_lt_top hθmeas htotal.ne)).exists
  let w := fun r ↦ q (polarPoint r θ) * r ^ (1 - σ)
  have hmap : MapsTo (fun r ↦ polarPoint r θ) (Ioo 0 ρ) A := by
    intro r hr
    change 0 < ‖polarPoint r θ‖ ∧ ‖polarPoint r θ‖ < ρ
    rw [polarPoint_norm, abs_of_pos hr.1]
    exact hr
  have hwc : ContinuousOn w (Ioo 0 ρ) :=
    (hqc.comp ((polarPoint_continuous.comp (continuous_id.prodMk continuous_const)).continuousOn) hmap).mul
      (continuous_id.continuousOn.rpow_const (fun r hr ↦ Or.inl hr.1.ne'))
  have hw0 : ∀ r ∈ Ioo 0 ρ, 0 ≤ w r := fun r hr ↦
    mul_nonneg (hermitianNormSq_nonneg _ _) (Real.rpow_nonneg hr.1.le _)
  have heq : (∫⁻ r in Ioo 0 ρ, ENNReal.ofReal r * Q (polarPoint r θ)) =
      ∫⁻ r in Ioo 0 ρ, ENNReal.ofReal (w r) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only [Q]
    rw [indicator_of_mem (hmap hr), polarPoint_norm, abs_of_pos hr.1,
      ← ENNReal.ofReal_mul hr.1.le]
    congr 1
    dsimp [w]
    have hp : r * r ^ (-σ) = r ^ (1 - σ) := by
      calc
        r * r ^ (-σ) = r ^ (1 : ℝ) * r ^ (-σ) := by rw [Real.rpow_one]
        _ = r ^ (1 + -σ) := (Real.rpow_add hr.1 _ _).symm
        _ = r ^ (1 - σ) := rfl
    rw [← hp]
    ring
  refine ⟨θ, hwc.aestronglyMeasurable measurableSet_Ioo, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem measurableSet_Ioo hw0)).mpr
  rwa [heq] at hfinite

end Yau.NodeProofs.D02RemovableAux
