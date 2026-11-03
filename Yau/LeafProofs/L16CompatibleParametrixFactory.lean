import Yau.LeafProofs.L16CompatibleInverseOperator

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

local instance compatibleFactory_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance compatibleFactory_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- A genuine source-linear solution factory from an actual source-linear
parametrix and its two proved residual bounds. All assertions concern the
actual functions and the actual differential operator on the closed cylinder. -/
theorem compatibleParametrix_linear_inverse {n : ℕ} {α T β CP : ℝ} {O : Set (Space n)}
    (hα : 0 < α) (hT : 0 ≤ T) (hβ : 0 < β) (hCP : 0 < CP)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (P D : compatibleHolderGraph α O T → Point n → ℝ)
    (hP : ∀ f,
      SchauderBound α (cylinder univ 0 T) (P f) (CP*‖f‖) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (P f p,spatialD (P f) p)) (CP*‖f‖))
    (hInitial : ∀ f x, P f (x,0) = 0)
    (hLateral : ∀ f x, x ∈ frontier O → ∀ t ∈ Icc 0 T, P f (x,t) = 0)
    (hPAdd : ∀ f g p, p ∈ cylinder univ 0 T → P (f+g) p = P f p+P g p)
    (hPSmul : ∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → P (c • f) p = c*P f p)
    (hOperator : ∀ f p, p ∈ cylinder (closure O) 0 T →
      linearOp (cylinder (closure O) 0 T) a b (P f) p = compatibleHolderFun f p+D f p)
    (hDAdd : ∀ f g p, p ∈ cylinder (closure O) 0 T → D (f+g) p = D f p+D g p)
    (hDSmul : ∀ (c : ℝ) f p, p ∈ cylinder (closure O) 0 T → D (c • f) p = c*D f p)
    (hCorner : ∀ f x, x ∈ frontier O → D f (x,0) = 0)
    (hRefined : ∀ f,
      HolderBound α (cylinder (closure O) 0 T) (D f) (‖f‖/4+β*‖f.val.val.1‖/4) ∧
      ∀ p ∈ cylinder (closure O) 0 T, |D f p| ≤ ‖f‖/(4*β)) :
    ∃ U : compatibleHolderGraph α O T → Point n → ℝ,
      (∀ f g p, p ∈ cylinder univ 0 T → U (f+g) p = U f p+U g p) ∧
      (∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → U (c • f) p = c*U f p) ∧
      ∀ f,
        SchauderBound α (cylinder univ 0 T) (U f) ((2*(1+β)*CP)*‖f‖) ∧
        HolderBound α (cylinder univ 0 T) (fun p => (U f p,spatialD (U f) p))
          ((2*(1+β)*CP)*‖f‖) ∧
        (∀ x, U f (x,0) = 0) ∧
        (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, U f (x,t) = 0) ∧
        ∀ p ∈ cylinder (closure O) 0 T,
          linearOp (cylinder (closure O) 0 T) a b (U f) p = compatibleHolderFun f p := by
  let E := compatibleHolderGraph α O T
  have hProjection (x : E) : ‖x.val.val.1‖ ≤ ‖x‖ := by
    change ‖x.val.val.1‖ ≤ max ‖x.val.val.1‖ ‖x.val.val.2‖
    exact le_max_left _ _
  have hBound (x : E) : HolderBound α (cylinder (closure O) 0 T) (D x)
      (((1+β)/4)*‖x‖) := by
    apply holderBound_mono_const (hRefined x).1
    have h := mul_le_mul_of_nonneg_left (hProjection x) hβ.le
    nlinarith only [h]
  let R : E →L[ℝ] E := compatibleHolderGraphLift hα hT D hBound hDAdd hDSmul hCorner
  have hREq (x : E) : EqOn (compatibleHolderFun (R x)) (D x)
      (cylinder (closure O) 0 T) :=
    compatibleHolderGraphLift_eqOn hα hT D hBound hDAdd hDSmul hCorner x
  have hStrong (x : E) : ‖R x‖ ≤ (1/4 : ℝ)*‖x‖+(β/4)*‖x.val.val.1‖ := by
    change ‖(R x).val‖ ≤ _
    apply holderGraph_norm_le_of_holderBound (R x).val
    have h := holderBound_congr_on (hRefined x).1 (fun p hp => (hREq x hp).symm)
    have hCost : ‖x‖/4+β*‖x.val.val.1‖/4 =
        (1/4 : ℝ)*‖x‖+(β/4)*‖x.val.val.1‖ := by ring
    rw [hCost] at h
    exact h
  have hSup (x : E) : ‖(R x).val.val.1‖ ≤ (1/(4*β))*‖x‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro p
    change |D x p.val| ≤ _
    convert (hRefined x).2 p.val p.property using 1; ring
  have hContract (x : E) : ‖R x‖+β*‖(R x).val.val.1‖ ≤
      (1/2 : ℝ)*(‖x‖+β*‖x.val.val.1‖) := by
    have h := add_le_add (hStrong x) (mul_le_mul_of_nonneg_left (hSup x) hβ.le)
    have hCancel : β*(1/(4*β)) = (1/4 : ℝ) := by field_simp [hβ.ne']
    rw [← mul_assoc β (1/(4*β)) ‖x‖,hCancel] at h
    have hNonneg := mul_nonneg hβ.le (norm_nonneg x.val.val.1)
    nlinarith only [h,hCancel,hNonneg]
  obtain ⟨G,hG,hCorrect⟩ := compatibleHolderGraph_linear_residual_correction R hβ.le hContract
  let U : E → Point n → ℝ := fun f => P (G f)
  refine ⟨U,?_,?_,?_⟩
  · intro f g p hp
    change P (G (f+g)) p = _
    rw [G.map_add]
    exact hPAdd _ _ p hp
  · intro c f p hp
    change P (G (c • f)) p = _
    rw [G.map_smul]
    exact hPSmul c _ p hp
  · intro f
    have hGF : ‖G f‖ ≤ 2*(1+β)*‖f‖ := (G.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hG (norm_nonneg f))
    have hBudget : CP*‖G f‖ ≤ (2*(1+β)*CP)*‖f‖ := by
      calc
        _ ≤ CP*(2*(1+β)*‖f‖) := mul_le_mul_of_nonneg_left hGF hCP.le
        _ = _ := by ring
    refine ⟨schauderBound_mono_const (hP (G f)).1 hBudget,
      holderBound_mono_const (hP (G f)).2 hBudget,hInitial (G f),hLateral (G f),?_⟩
    intro p hp
    have hEval := congrArg (fun x : E => compatibleHolderFun x p) (hCorrect f)
    rw [compatibleHolderFun_add,Pi.add_apply,hREq (G f) hp] at hEval
    exact (hOperator (G f) p hp).trans hEval

end Yau.LeafProofs.L16Aux
