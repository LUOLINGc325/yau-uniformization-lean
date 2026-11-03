import Yau.Proofs.C07CurveLength
import Yau.Proofs.C07ShortLift
import Yau.Proofs.C07JointLift

/-! The same uniformly short family of actual curves has a joint continuous lift. -/

open scoped Manifold Topology

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint Set MeasureTheory

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_joint_short_lift {A : Type*} [TopologicalSpace A]
    {k₀ k₁ : HermitianField M} {o : M.Carrier} {x : A → M.Carrier}
    {Φ : ComplexVector n → M.Carrier} {r c C D L : ℝ}
    (hk₁ : MetricSmooth k₁) (hr : 0 < r) (hc : 0 < c)
    (hΦ : UnitaryChart k₁ o Φ r c C)
    (γ : ∀ a, IntegrableCurve k₀ o (x a)) (H : C(unitInterval × A, M.Carrier))
    (hH : ∀ p, H p = (γ p.2).1 p.1) (hD : 0 ≤ D)
    (horder : ∀ a, ∀ t ∈ Icc (0 : ℝ) 1,
      HermLE (gMat k₁ ((γ a).1 t)) ((D : ℂ) • gMat k₀ ((γ a).1 t)))
    (hlength : ∀ a, curveLength k₀ (γ a).1 ≤ L)
    (hshort : Real.sqrt D * L < Real.sqrt (2 * c) * r) :
    ∃ E : unitInterval × A → ComplexVector n,
      Continuous E ∧ (∀ a, E (0, a) = 0) ∧
      (∀ p, E p ∈ Metric.ball 0 r ∧ Φ (E p) = H p) ∧
      ∀ p, ‖E p‖ ≤ (Real.sqrt (2 * c))⁻¹ * Real.sqrt D * L := by
  classical
  have hα : 0 ≤ (Real.sqrt (2 * c))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hex (a : A) : ∃ η : ℝ → ComplexVector n,
      ContinuousOn η (Icc (0 : ℝ) 1) ∧ η 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, η t ∈ Metric.ball 0 r ∧ Φ (η t) = (γ a).1 t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ‖η t‖ ≤ (Real.sqrt (2 * c))⁻¹ * Real.sqrt D * L := by
    have hcmp := C07CurveLengthAux.curve_length_comparison hk₁ (γ a) hD (horder a)
    let δ : IntegrableCurve k₁ o (x a) := ⟨(γ a).1, hcmp.1⟩
    have hδlength : curveLength k₁ δ.1 ≤ Real.sqrt D * L :=
      hcmp.2.trans (mul_le_mul_of_nonneg_left (hlength a) (Real.sqrt_nonneg _))
    obtain ⟨η, hη, hη₀, hηp, hηbound⟩ :=
      C07ShortLiftAux.short_curve_lift hr hc hΦ δ (hδlength.trans_lt hshort)
    refine ⟨η, hη, hη₀, hηp, ?_⟩
    intro t ht
    calc
      ‖η t‖ ≤ (Real.sqrt (2 * c))⁻¹ * (∫ u in Icc 0 t, curveSpeed k₁ δ.1 u) := hηbound t ht
      _ ≤ (Real.sqrt (2 * c))⁻¹ * curveLength k₁ δ.1 :=
        mul_le_mul_of_nonneg_left (C07ShortLiftAux.prefix_integral_le_length δ ht) hα
      _ ≤ (Real.sqrt (2 * c))⁻¹ * (Real.sqrt D * L) :=
        mul_le_mul_of_nonneg_left hδlength hα
      _ = _ := (mul_assoc _ _ _).symm
  choose η hη hη₀ hηp hηbound using hex
  let E : unitInterval × A → ComplexVector n := fun p => η p.2 p.1
  have hstart : Continuous (fun a => E (0, a)) :=
    continuous_const.congr fun a => (hη₀ a).symm
  have hrows : ∀ a, Continuous (fun t => E (t, a)) :=
    fun a => (hη a).comp_continuous continuous_subtype_val (fun t => t.2)
  have hEp (p : unitInterval × A) : E p ∈ Metric.ball 0 r ∧ Φ (E p) = H p :=
    ⟨(hηp p.2 p.1 p.1.2).1, (hηp p.2 p.1 p.1.2).2.trans (hH p).symm⟩
  exact ⟨E, chart_lift_joint_continuous hΦ.1 H E
    (fun p => (hEp p).1) (fun p => (hEp p).2) hstart hrows,
    hη₀, hEp, fun p => hηbound p.2 p.1 p.1.2⟩

end Yau.Proofs.C07Aux
