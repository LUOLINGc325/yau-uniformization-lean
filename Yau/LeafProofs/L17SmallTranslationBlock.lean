import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SmallTranslationAux

variable {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def blockTriangularEquiv (A : P →L[ℝ] Y) (B : X ≃L[ℝ] Y) : (P × X) ≃L[ℝ] (P × Y) where
  toLinearEquiv := {
    toFun := fun q => (q.1,A q.1+B q.2)
    invFun := fun q => (q.1,B.symm (q.2-A q.1))
    left_inv := by intro q; rcases q with ⟨p,x⟩; simp
    right_inv := by intro q; rcases q with ⟨p,y⟩; simp
    map_add' := by intro q r; ext <;> simp <;> abel
    map_smul' := by intro c q; ext <;> simp [smul_add] }
  continuous_toFun := continuous_fst.prodMk
    ((A.continuous.comp continuous_fst).add (B.continuous.comp continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (B.symm.continuous.comp (continuous_snd.sub (A.continuous.comp continuous_fst)))

@[simp] theorem blockTriangularEquiv_apply (A : P →L[ℝ] Y) (B : X ≃L[ℝ] Y) (p : P) (x : X) :
    blockTriangularEquiv A B (p,x)=(p,A p+B x) := rfl

@[simp] theorem blockTriangularEquiv_symm_apply (A : P →L[ℝ] Y) (B : X ≃L[ℝ] Y) (p : P) (y : Y) :
    (blockTriangularEquiv A B).symm (p,y)=(p,B.symm (y-A p)) := rfl

end Yau.LeafProofs.L17SmallTranslationAux
