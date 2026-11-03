import Yau.Proofs.C07RadialCurve
import Yau.Proofs.C07ShortLift
import Yau.Proofs.C07JointLift

/-! The actual short radial lifts give a transition on one fixed whole ball. -/

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set MeasureTheory

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_continuous_transition
    {k₀ k₁ : HermitianField M} {o : M.Carrier}
    {Φ Ψ : ComplexVector n → M.Carrier} {r R c C : ℝ}
    (hk₁ : MetricSmooth k₁)
    (horder : ∀ x, HermLE (gMat k₁ x) (gMat k₀ x))
    (hr : 0 < r) (hR : 0 < R) (hRr : R ≤ r) (hc : 0 < c) (hC : 0 < C)
    (hΦ : UnitaryChart k₀ o Φ r c C) (hΨ : UnitaryChart k₁ o Ψ r c C)
    (hshort : Real.sqrt (2 * C) * R ≤ Real.sqrt (2 * c) * r) :
    ∃ F : ComplexVector n → ComplexVector n,
      ContinuousOn F (Metric.ball 0 R) ∧ F 0 = 0 ∧
      ∀ z ∈ Metric.ball 0 R, F z ∈ Metric.ball 0 r ∧ Ψ (F z) = Φ z ∧
        ‖F z‖ ≤ ((Real.sqrt (2 * c))⁻¹ * Real.sqrt (2 * C)) * ‖z‖ := by
  classical
  have hα : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.2 (by positivity)
  have hβ : 0 < Real.sqrt (2 * C) := Real.sqrt_pos.2 (by positivity)
  have hex (z : Metric.ball (0 : ComplexVector n) R) :
      ∃ η : ℝ → ComplexVector n,
        ContinuousOn η (Icc (0 : ℝ) 1) ∧ η 0 = 0 ∧
        (∀ a ∈ Icc (0 : ℝ) 1, η a ∈ Metric.ball 0 r ∧ Ψ (η a) = Φ ((a : ℂ) • z.1)) ∧
        ‖η 1‖ ≤ ((Real.sqrt (2 * c))⁻¹ * Real.sqrt (2 * C)) * ‖z.1‖ := by
    have hzR : ‖z.1‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using z.2
    have hzr : ‖z.1‖ < r := hzR.trans_le hRr
    obtain ⟨γ, hγ, hlength⟩ := C07RadialCurveAux.exists_radial_curve hk₁ horder hC hΦ hzr
    have hshortγ : curveLength k₁ γ.1 < Real.sqrt (2 * c) * r :=
      hlength.trans_lt ((mul_lt_mul_of_pos_left hzR hβ).trans_le hshort)
    obtain ⟨η, hη, hη₀, hηp, hηbound⟩ :=
      C07ShortLiftAux.short_curve_lift hr hc hΨ γ hshortγ
    refine ⟨η, hη, hη₀, ?_, ?_⟩
    · intro a ha
      exact ⟨(hηp a ha).1, (hηp a ha).2.trans (hγ a ha)⟩
    · have h := hηbound 1 ⟨zero_le_one, le_rfl⟩
      change ‖η 1‖ ≤ (Real.sqrt (2 * c))⁻¹ * curveLength k₁ γ.1 at h
      calc
        ‖η 1‖ ≤ (Real.sqrt (2 * c))⁻¹ * curveLength k₁ γ.1 := h
        _ ≤ (Real.sqrt (2 * c))⁻¹ * (Real.sqrt (2 * C) * ‖z.1‖) :=
          mul_le_mul_of_nonneg_left hlength (inv_nonneg.mpr hα.le)
        _ = _ := (mul_assoc _ _ _).symm
  choose η hη hη₀ hηp hηbound using hex
  let E : unitInterval × Metric.ball (0 : ComplexVector n) R → ComplexVector n :=
    fun p => η p.2 p.1
  have hinside (p : unitInterval × Metric.ball (0 : ComplexVector n) R) :
      ((p.1 : ℝ) : ℂ) • p.2.1 ∈ Metric.ball (0 : ComplexVector n) r := by
    have hzR : ‖p.2.1‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using p.2.2
    simp only [Metric.mem_ball, dist_zero_right]
    calc
      ‖((p.1 : ℝ) : ℂ) • p.2.1‖ = (p.1 : ℝ) * ‖p.2.1‖ := by
        rw [norm_smul, Complex.norm_of_nonneg p.1.2.1]
      _ ≤ ‖p.2.1‖ := mul_le_of_le_one_left (norm_nonneg _) p.1.2.2
      _ < r := hzR.trans_le hRr
  let H : C(unitInterval × Metric.ball (0 : ComplexVector n) R, M.Carrier) :=
    ⟨fun p => Φ (((p.1 : ℝ) : ℂ) • p.2.1),
      hΦ.1.1.continuousOn.comp_continuous (by fun_prop) hinside⟩
  have hstart : Continuous (fun z => E (0, z)) :=
    continuous_const.congr fun z => (hη₀ z).symm
  have hrows : ∀ z, Continuous (fun a => E (a, z)) :=
    fun z => (hη z).comp_continuous continuous_subtype_val (fun a => a.2)
  have hE : Continuous E := chart_lift_joint_continuous hΨ.1 H E
    (fun p => (hηp p.2 p.1 p.1.2).1)
    (fun p => (hηp p.2 p.1 p.1.2).2) hstart hrows
  let F : ComplexVector n → ComplexVector n := fun z =>
    if hz : z ∈ Metric.ball 0 R then η ⟨z, hz⟩ 1 else 0
  have hF (z : Metric.ball (0 : ComplexVector n) R) : F z.1 = η z 1 := by
    simp only [F, dite_eq_left z.2]
  have hFc : ContinuousOn F (Metric.ball 0 R) := by
    have hmap : Continuous
        (fun z : Metric.ball (0 : ComplexVector n) R => ((1 : unitInterval), z)) :=
      continuous_const.prodMk continuous_id
    have hc' : Continuous (fun z : Metric.ball (0 : ComplexVector n) R => η z 1) := by
      simpa [E, Function.comp_def] using hE.comp hmap
    exact continuousOn_iff_continuous_domRestrict.mpr
      (hc'.congr fun z => (hF z).symm)
  have hFpoint : ∀ z ∈ Metric.ball 0 R,
      F z ∈ Metric.ball 0 r ∧ Ψ (F z) = Φ z ∧
        ‖F z‖ ≤ ((Real.sqrt (2 * c))⁻¹ * Real.sqrt (2 * C)) * ‖z‖ := by
    intro z hz
    rw [hF ⟨z, hz⟩]
    refine ⟨(hηp ⟨z, hz⟩ 1 ⟨zero_le_one, le_rfl⟩).1, ?_, hηbound ⟨z, hz⟩⟩
    simpa only [Complex.ofReal_one, one_smul] using
      (hηp ⟨z, hz⟩ 1 ⟨zero_le_one, le_rfl⟩).2
  refine ⟨F, hFc, ?_, hFpoint⟩
  have hn := (hFpoint 0 (Metric.mem_ball_self hR)).2.2
  simp only [norm_zero, mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

end Yau.Proofs.C07Aux
