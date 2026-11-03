import Yau.Proofs.V02SeqUpperZero
import Yau.Proofs.V03LocalizationNonempty

/-! Test the actual localized infimum against every deformed slice.
Only after fixing the radius is the minimizing-sequence limit taken. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter MeasureTheory

noncomputable section
namespace Yau.Blueprint.V02Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

theorem minimizingSequence_gap_tendsto {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {F : ℕ → VariationDisc X}
    (hF : MinimizingSequence d j ε F) :
    Tendsto (fun ν => penalizedFunctional d j ε (F ν) -
      (localizedInfimum d j ε).toReal) atTop (𝓝 0) := by
  have hμ := V03Proof.localizedInfimum_finite_of_nonempty hd ⟨F 0, hF.1 0⟩ hε
  have ht := (EReal.tendsto_toReal hμ.2 hμ.1).comp hF.2
  have htR : Tendsto (fun ν => penalizedFunctional d j ε (F ν)) atTop
      (𝓝 (localizedInfimum d j ε).toReal) := by
    simpa only [Function.comp_def, EReal.toReal_coe] using ht
  simpa only [sub_self] using htR.sub_const (localizedInfimum d j ε).toReal

theorem infimum_toReal_le_cost {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {F : VariationDisc X}
    (hF : AdmissibleVariationDisc d j F) :
    (localizedInfimum d j ε).toReal ≤ penalizedFunctional d j ε F := by
  have hμ := V03Proof.localizedInfimum_finite_of_nonempty hd ⟨F, hF⟩ hε
  simpa only [EReal.toReal_coe] using EReal.toReal_le_toReal
    (V03Proof.localizedInfimum_le ε hF) hμ.1 (by simp)

theorem minimizingSequence_gap_nonneg {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {ε : ℝ} (hε : 0 ≤ ε) {F : ℕ → VariationDisc X}
    (hF : MinimizingSequence d j ε F) (ν : ℕ) :
    0 ≤ penalizedFunctional d j ε (F ν) - (localizedInfimum d j ε).toReal :=
  sub_nonneg.mpr (infimum_toReal_le_cost hd hε (hF.1 ν))

theorem circleAverage_lower_of_pointwise {f : ℝ → ℝ} (hf : Continuous f)
    {μ : ℝ} (hlower : ∀ θ, μ ≤ f θ) : μ ≤ circleAverage f := by
  have hc : circleAverage (fun _ => μ) = μ := by
    unfold circleAverage
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), one_mul]
  rw [← hc]
  unfold circleAverage
  apply mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      intervalIntegrable_const (hf.intervalIntegrable _ _) (fun θ _ => hlower θ))
  positivity

/-- This uses the unchanged whole penalized functional and the literal
nested mixed Wirtinger derivative in the frozen realization contract. -/
theorem realized_negative_mixed_le_gap
    {d : VariationData X q} (hd : VariationSetup d) {j a : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) {F : VariationDisc X} {E : ℂ → CotangentMatrix n}
    {l : ℂ → CotangentIndex n → ℂ} {h α : ℂ → ℂ}
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {r C ρ : ℝ}
    (hR : RealizesFirstField d j a F E l h α fz r)
    (hρ : 0 < ρ) (hρr : ρ < r)
    (hcont : Continuous (fun θ =>
      penalizedFunctional d j ε {F with f := fz ((ρ : ℂ) * circlePoint θ)}))
    (hTaylor :
      |circleAverage (fun θ =>
        penalizedFunctional d j ε {F with f := fz ((ρ : ℂ) * circlePoint θ)}) -
        penalizedFunctional d j ε {F with f := fz 0} - ρ ^ 2 *
          V03Proof.mixedReal (fun z => penalizedFunctional d j ε {F with f := fz z})| ≤
        C * ρ ^ 3) :
    -V03Proof.mixedReal (fun z => penalizedFunctional d j ε {F with f := fz z}) ≤
      (penalizedFunctional d j ε F - (localizedInfimum d j ε).toReal) / ρ ^ 2 + C * ρ := by
  have hlower : (localizedInfimum d j ε).toReal ≤
      circleAverage (fun θ =>
        penalizedFunctional d j ε {F with f := fz ((ρ : ℂ) * circlePoint θ)}) := by
    apply circleAverage_lower_of_pointwise hcont
    intro θ
    apply infimum_toReal_le_cost hd hε
    apply hR.2.1
    simpa only [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ, V03Proof.circlePoint_norm, mul_one] using hρr
  have hzero : ({F with f := fz 0} : VariationDisc X) = F := by
    rw [hR.1.2.1]
  have ht := negative_mixed_le_gap_of_taylor hρ hlower hTaylor
  simpa only [hzero] using ht

end Yau.Blueprint.V02Proof
