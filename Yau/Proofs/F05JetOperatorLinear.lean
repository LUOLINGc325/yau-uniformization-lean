import Yau.Proofs.F05JetOperator

/-! At each physical point the computed original differential operator is
an actual continuous linear evaluation of the complete jet graph. -/

open Set
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

def F05JetOperatorEval (A : AtlasData M) (c : M.Carrier → ℝ → ℝ)
    (h : ℝ → HermitianField M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (i : Fin A.count) (p : F05Q A i T) : F05CompatibleJetGraph A α hT →L[ℝ] ℝ :=
  (F05GlobalTimeEval A α hT i p).comp (F05CompatibleJetGraph A α hT).subtypeL -
    c (lift A i p.val.1) p.val.2 •
      ((∑ a,∑ b, flatA (h p.val.2) A i p.val a b •
        ((ContinuousLinearMap.apply ℝ ℝ (realVec b)).comp
          ((ContinuousLinearMap.apply ℝ (F05Dual n) (realVec a)).comp
            ((F05GlobalHessianEval A α hT i p).comp (F05CompatibleJetGraph A α hT).subtypeL))))+
        ∑ a,flatB (h p.val.2) A i p.val a •
          ((ContinuousLinearMap.apply ℝ ℝ (realVec a)).comp
            ((F05GlobalGradientEval A α hT i p).comp (F05CompatibleJetGraph A α hT).subtypeL)))

theorem F05JetOperatorEval_apply (A : AtlasData M) (c : M.Carrier → ℝ → ℝ)
    (h : ℝ → HermitianField M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (i : Fin A.count) (p : F05Q A i T) (u : F05CompatibleJetGraph A α hT) :
    F05JetOperatorEval A c h α hT i p u = F05JetOperator A c h α hT u i p.val := by
  simp only [F05JetOperatorEval,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply,smul_eq_mul]
  unfold F05JetOperator
  rw [F05BCFFun_apply _ p,F05BCFFun_apply _ p,F05BCFFun_apply _ p]
  rfl

theorem F05JetOperator_add (A : AtlasData M) (c : M.Carrier → ℝ → ℝ)
    (h : ℝ → HermitianField M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (u v : F05CompatibleJetGraph A α hT) (i : Fin A.count) (p : F05Q A i T) :
    F05JetOperator A c h α hT (u+v) i p.val =
      F05JetOperator A c h α hT u i p.val+F05JetOperator A c h α hT v i p.val := by
  rw [← F05JetOperatorEval_apply A c h α hT i p (u+v),map_add,
    F05JetOperatorEval_apply,F05JetOperatorEval_apply]

theorem F05JetOperator_smul (A : AtlasData M) (c : M.Carrier → ℝ → ℝ)
    (h : ℝ → HermitianField M) (α : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (d : ℝ) (u : F05CompatibleJetGraph A α hT) (i : Fin A.count) (p : F05Q A i T) :
    F05JetOperator A c h α hT (d • u) i p.val = d*F05JetOperator A c h α hT u i p.val := by
  rw [← F05JetOperatorEval_apply A c h α hT i p (d • u),map_smul,
    F05JetOperatorEval_apply,smul_eq_mul]

end Yau.Proofs.F05Aux
