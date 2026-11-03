import Yau.LeafProofs.L16CompatibleHolderGraph

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

local instance compatibleActualResidual_group {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedAddCommGroup (compatibleHolderGraph α O T) := inferInstance
local instance compatibleActualResidual_space {n : ℕ} (α : ℝ) (O : Set (Space n)) (T : ℝ) :
    NormedSpace ℝ (compatibleHolderGraph α O T) := inferInstance

/-- The literal original-operator residual, on the actual closed cylinder. -/
def compatibleActualResidual {n : ℕ} {α T : ℝ} (O : Set (Space n))
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (P : compatibleHolderGraph α O T → Point n → ℝ)
    (f : compatibleHolderGraph α O T) (p : Point n) : ℝ :=
  linearOp (cylinder (closure O) 0 T) a b (P f) p-compatibleHolderFun f p

/-- Actual ambient pointwise additivity and actual regularity are enough
for additivity of the literal residual on the original closed domain. -/
theorem compatibleActualResidual_add {n : ℕ} {α T : ℝ} {O : Set (Space n)}
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (P : compatibleHolderGraph α O T → Point n → ℝ)
    (hP : ∀ f, C2 (cylinder univ 0 T) (P f))
    (hAdd : ∀ f g p, p ∈ cylinder univ 0 T → P (f+g) p = P f p+P g p)
    (f g : compatibleHolderGraph α O T) {p : Point n}
    (hp : p ∈ cylinder (closure O) 0 T) :
    compatibleActualResidual O a b P (f+g) p =
      compatibleActualResidual O a b P f p+compatibleActualResidual O a b P g p := by
  have hEq : EqOn (P (f+g)) (fun q => P f q+P g q) (cylinder univ 0 T) := hAdd f g
  have hpA : p ∈ cylinder univ 0 T := ⟨mem_univ _,hp.2⟩
  unfold compatibleActualResidual
  simp only [linearOp_cylinder_restrict_space a b _ hp]
  rw [linearOp_congr_cylinder_univ hEq a b hpA,
    linearOp_add (a := a) (b := b) (hP f) (hP g) hpA,compatibleHolderFun_add]
  simp only [Pi.add_apply]
  ring

/-- Actual ambient scalar linearity gives the true residual scalar identity;
no extension of the residual off the compatible graph is introduced. -/
theorem compatibleActualResidual_smul {n : ℕ} {α T : ℝ} {O : Set (Space n)}
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (P : compatibleHolderGraph α O T → Point n → ℝ)
    (hP : ∀ f, C2 (cylinder univ 0 T) (P f))
    (hSmul : ∀ (c : ℝ) f p, p ∈ cylinder univ 0 T → P (c • f) p = c*P f p)
    (c : ℝ) (f : compatibleHolderGraph α O T) {p : Point n}
    (hp : p ∈ cylinder (closure O) 0 T) :
    compatibleActualResidual O a b P (c • f) p = c*compatibleActualResidual O a b P f p := by
  have hEq : EqOn (P (c • f)) (c • P f) (cylinder univ 0 T) := hSmul c f
  have hpA : p ∈ cylinder univ 0 T := ⟨mem_univ _,hp.2⟩
  unfold compatibleActualResidual
  simp only [linearOp_cylinder_restrict_space a b _ hp]
  rw [linearOp_congr_cylinder_univ hEq a b hpA,
    linearOp_const_smul (a := a) (b := b) (hP f) c hpA,compatibleHolderFun_smul]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

end Yau.LeafProofs.L16Aux
