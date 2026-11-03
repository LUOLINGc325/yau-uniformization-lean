import Yau.LeafProofs.L17BootstrapClosedSlabJets

open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapJetEvaluationAux
open L17BootstrapClosedSlabAux

variable {E X Y Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

abbrev jetAsCLM {k : ℕ} (A : Jet E X (k+1)) : E →L[ℝ] Jet E X k := A

def jetMap (L : X →L[ℝ] Y) : (k : ℕ) → Jet E X k →L[ℝ] Jet E Y k
  | 0 => L
  | k+1 => (ContinuousLinearMap.compL ℝ E (Jet E X k) (Jet E Y k)) (jetMap L k)

@[simp] theorem jetMap_zero_apply (L : X →L[ℝ] Y) (A : X) : jetMap (E := E) L 0 A=L A := rfl

@[simp] theorem jetMap_succ_apply (L : X →L[ℝ] Y) (k : ℕ) (A : Jet E X (k+1)) (a : E) :
    jetAsCLM (jetMap (E := E) L (k+1) A) a=jetMap (E := E) L k (jetAsCLM A a) := rfl

theorem jetMap_norm_le (L : X →L[ℝ] Y) (k : ℕ) : ‖jetMap (E := E) L k‖≤‖L‖ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro A
      exact ((jetMap (E := E) L k).opNorm_comp_le A).trans
        (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

@[simp] theorem jetMap_add (L : X →L[ℝ] Y) (k : ℕ) (A B : Jet E X k) :
    jetMap (E := E) L k (A+B)=jetMap L k A+jetMap L k B := (jetMap L k).map_add A B

@[simp] theorem jetMap_smul (L : X →L[ℝ] Y) (k : ℕ) (r : ℝ) (A : Jet E X k) :
    jetMap (E := E) L k (r • A)=r • jetMap L k A := (jetMap L k).map_smul r A

theorem jetMap_comp (L : X →L[ℝ] Y) (M : Y →L[ℝ] Z) (k : ℕ) :
    jetMap (E := E) (M.comp L) k=(jetMap M k).comp (jetMap L k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      apply ContinuousLinearMap.ext
      intro A
      apply ContinuousLinearMap.ext
      intro a
      change jetMap (M.comp L) k (jetAsCLM A a)=jetMap M k (jetMap L k (jetAsCLM A a))
      rw [ih]
      rfl

end Yau.LeafProofs.L17BootstrapJetEvaluationAux
