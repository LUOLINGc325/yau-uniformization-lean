import Yau.Proofs.C02CurvaturePositivity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! A dimension-dependent trace bound on the entire nonnegative bisectional
coefficient cone. Compactness is used only in this finite-dimensional space. -/

noncomputable section
open Set
open scoped Matrix ComplexOrder Matrix.Norms.Elementwise
namespace Yau.Blueprint.C02Proof
variable {n : ℕ}

theorem curvaturePartial_real_smul (s : ℝ) (C : CurvatureArray n) (v : Fin n → ℂ) :
    curvaturePartial (s • C) v = s • curvaturePartial C v := by
  ext i j
  simp only [curvaturePartial, Pi.smul_apply, Matrix.smul_apply, Finset.smul_sum,
    mul_smul_comm, smul_mul_assoc]

theorem curvatureTrace_real_smul (s : ℝ) (C : CurvatureArray n) :
    curvatureTrace (s • C) = s * curvatureTrace C := by
  simp only [curvatureTrace, curvatureRicciPartial, Matrix.trace, Matrix.diag,
    Pi.smul_apply, Matrix.smul_apply, Complex.re_sum, Complex.smul_re,
    smul_eq_mul, Finset.mul_sum]

theorem CurvaturePositive.real_smul {C : CurvatureArray n} (hC : CurvaturePositive C)
    (s : ℝ) (hs : 0 ≤ s) : CurvaturePositive (s • C) := by
  constructor
  · intro i j k l
    simp only [Pi.smul_apply, Matrix.smul_apply, star_smul, star_trivial, hC.1]
  · intro v w
    rw [curvaturePartial_real_smul, Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re]
    exact mul_nonneg hs (hC.2 v w)

theorem continuous_curvatureTrace : Continuous (curvatureTrace (n := n)) := by
  unfold curvatureTrace curvatureRicciPartial Matrix.trace Matrix.diag
  fun_prop

theorem isClosed_curvaturePositive : IsClosed {C : CurvatureArray n | CurvaturePositive C} := by
  simp only [CurvaturePositive, ofPred_and, ofPred_forall]
  refine (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
    isClosed_iInter fun l => isClosed_eq (by fun_prop) (by fun_prop)).inter ?_
  refine isClosed_iInter fun v => isClosed_iInter fun w => ?_
  apply isClosed_le continuous_const
  unfold curvaturePartial dotProduct Matrix.mulVec
  fun_prop

theorem exists_curvature_coefficient_trace_bound (n : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ C : CurvatureArray n,
      CurvaturePositive C → ‖C‖ ≤ D * curvatureTrace C := by
  let : FiniteDimensional ℝ (CurvatureArray n) := by
    let e : CurvatureArray n ≃ₗ[ℝ] (Fin n → Fin n → Fin n → Fin n → ℂ) :=
      { toFun := fun C i j k l => C i j k l
        invFun := fun C i j k l => C i j k l
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact FiniteDimensional.of_injective e.toLinearMap e.injective
  let : ProperSpace (CurvatureArray n) := FiniteDimensional.proper ℝ (CurvatureArray n)
  let S : Set (CurvatureArray n) := {C | CurvaturePositive C} ∩ Metric.sphere 0 1
  have hS : IsCompact S := (isCompact_sphere (0 : CurvatureArray n) 1).of_isClosed_subset
    (isClosed_curvaturePositive.inter Metric.isClosed_sphere) inter_subset_right
  have hTracePos (C : CurvatureArray n) (hC : C ∈ S) : 0 < curvatureTrace C := by
    apply hC.1.trace_pos
    intro hz
    have hn : ‖C‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hC.2
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hInverse : ContinuousOn (fun C : CurvatureArray n => (curvatureTrace C)⁻¹) S :=
    continuous_curvatureTrace.continuousOn.inv₀ (fun C hC => (hTracePos C hC).ne')
  obtain ⟨D, hD⟩ := hS.bddAbove_image hInverse
  refine ⟨max D 1, lt_of_lt_of_le zero_lt_one (le_max_right D 1), ?_⟩
  intro C hC
  by_cases hCzero : C = 0
  · rw [hCzero, norm_zero]
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right D 1)))
      ((hCzero ▸ hC).trace_nonneg)
  have hNorm : 0 < ‖C‖ := norm_pos_iff.mpr hCzero
  let E : CurvatureArray n := ‖C‖⁻¹ • C
  have hECone : CurvaturePositive E := hC.real_smul _ (inv_nonneg.mpr hNorm.le)
  have hENorm : ‖E‖ = 1 := by
    dsimp only [E]
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hNorm.le), inv_mul_cancel₀ hNorm.ne']
  have hES : E ∈ S := ⟨hECone, by simpa only [Metric.mem_sphere, dist_zero_right] using hENorm⟩
  have hInvBound : (curvatureTrace E)⁻¹ ≤ D := hD (mem_image_of_mem _ hES)
  have hTrace : 0 < curvatureTrace C := hC.trace_pos hCzero
  have hRatio : ‖C‖ / curvatureTrace C ≤ D := by
    have hEq : (curvatureTrace E)⁻¹ = ‖C‖ / curvatureTrace C := by
      dsimp only [E]
      rw [curvatureTrace_real_smul]
      field_simp
    exact hEq ▸ hInvBound
  exact ((div_le_iff₀ hTrace).mp hRatio).trans
    (mul_le_mul_of_nonneg_right (le_max_left D 1) hTrace.le)

end Yau.Blueprint.C02Proof
