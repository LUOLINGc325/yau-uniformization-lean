import Yau.LeafProofs.L17BootstrapClosedSlabProduct

open Set Filter Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapClosedSlabAux

universe u
abbrev RealNormedModel : Type (u+1) :=
  Σ V : Type u, Σ g : NormedAddCommGroup V, @NormedSpace ℝ V _ g.toSeminormedAddCommGroup

variable (E F : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def jetModel : ℕ → RealNormedModel.{u}
  | 0 => ⟨F,inferInstance,inferInstance⟩
  | k+1 =>
    let V := (jetModel k).1
    letI : NormedAddCommGroup V := (jetModel k).2.1
    letI : NormedSpace ℝ V := (jetModel k).2.2
    ⟨E →L[ℝ] V,inferInstance,inferInstance⟩

abbrev Jet (k : ℕ) := (jetModel E F k).1

instance jetNormedAddCommGroup (k : ℕ) : NormedAddCommGroup (Jet E F k) := (jetModel E F k).2.1
instance jetNormedSpace (k : ℕ) : NormedSpace ℝ (Jet E F k) := (jetModel E F k).2.2

instance jetCompleteSpace [CompleteSpace F] (k : ℕ) : CompleteSpace (Jet E F k) := by
  induction k with
  | zero => exact (inferInstance : CompleteSpace F)
  | succ k hk =>
      letI : CompleteSpace (Jet E F k) := hk
      change CompleteSpace (E →L[ℝ] Jet E F k)
      infer_instance

theorem Jet_zero : Jet E F 0=F := rfl
theorem Jet_succ (k : ℕ) : Jet E F (k+1)=(E →L[ℝ] Jet E F k) := rfl

def productDerivativeCLM : ((E →L[ℝ] F) × F) →L[ℝ] ((E × ℝ) →L[ℝ] F) :=
  (((ContinuousLinearMap.compL ℝ (E × ℝ) E F).flip (ContinuousLinearMap.fst ℝ E ℝ)).comp
    (ContinuousLinearMap.fst ℝ (E →L[ℝ] F) F))+
  (((ContinuousLinearMap.smulRightL ℝ (E × ℝ) F) (ContinuousLinearMap.snd ℝ E ℝ)).comp
    (ContinuousLinearMap.snd ℝ (E →L[ℝ] F) F))

theorem productDerivativeCLM_apply (A : E →L[ℝ] F) (b : F) :
    productDerivativeCLM E F (A,b)=A.comp (ContinuousLinearMap.fst ℝ E ℝ)+
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight b := by
  apply ContinuousLinearMap.ext
  intro p
  simp [productDerivativeCLM]

end Yau.LeafProofs.L17BootstrapClosedSlabAux
