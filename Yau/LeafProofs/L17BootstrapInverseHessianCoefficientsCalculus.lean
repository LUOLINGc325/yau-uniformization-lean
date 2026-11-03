import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Finite continuous-linear inverse Hessian operators and partial derivative calculus. -/

noncomputable section
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 1000000

namespace Yau.LeafProofs.L17BootstrapInverseHessianCoefficientsAux

variable {Param E F : Type*}
  [NormedAddCommGroup Param] [NormedSpace ℝ Param]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- These aliases retain the standard nested operator norms and stabilize instance search. -/
abbrev Form1 (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] := E →L[ℝ] F
abbrev Form2 (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] := E →L[ℝ] Form1 E F

instance form1NormedAddCommGroup : NormedAddCommGroup (Form1 E F) :=
  ContinuousLinearMap.toNormedAddCommGroup
instance form1NormedSpace : NormedSpace ℝ (Form1 E F) :=
  ContinuousLinearMap.toNormedSpace
instance form2NormedAddCommGroup : NormedAddCommGroup (Form2 E F) :=
  ContinuousLinearMap.toNormedAddCommGroup
instance form2NormedSpace : NormedSpace ℝ (Form2 E F) :=
  ContinuousLinearMap.toNormedSpace
instance form1EndNormedAddCommGroup : NormedAddCommGroup (Form1 E F →L[ℝ] Form1 E F) :=
  ContinuousLinearMap.toNormedAddCommGroup
instance form1EndNormedSpace : NormedSpace ℝ (Form1 E F →L[ℝ] Form1 E F) :=
  ContinuousLinearMap.toNormedSpace
instance form2EndNormedAddCommGroup : NormedAddCommGroup (Form2 E F →L[ℝ] Form2 E F) :=
  ContinuousLinearMap.toNormedAddCommGroup
instance form2EndNormedSpace : NormedSpace ℝ (Form2 E F →L[ℝ] Form2 E F) :=
  ContinuousLinearMap.toNormedSpace
instance form1To2NormedAddCommGroup : NormedAddCommGroup (Form1 E F →L[ℝ] Form2 E F) :=
  ContinuousLinearMap.toNormedAddCommGroup
instance form1To2NormedSpace : NormedSpace ℝ (Form1 E F →L[ℝ] Form2 E F) :=
  ContinuousLinearMap.toNormedSpace

theorem partial_fderiv_contDiffAt {f : Param × E → F} {p : Param × E}
    (hf : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞ (fun q : Param × E => fderiv ℝ (fun y => f (q.1,y)) q.2) p := by
  have hcomp : ContDiffAt ℝ ∞ (fun a : (Param × E) × E => f (a.1.1,a.2)) (p,p.2) :=
    hf.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact ContDiffAt.fderiv (𝕜 := ℝ)
    (f := fun (q : Param × E) (y : E) => f (q.1,y))
    (g := fun q : Param × E => q.2) hcomp contDiffAt_snd
    (by simp : (∞ : ℕ∞ω)+1 ≤ ∞)

def hessianPrecompositionCLM (L : E →L[ℝ] E) :
    (Form2 E F) →L[ℝ] Form2 E F :=
  (ContinuousLinearMap.compL ℝ E (Form1 E F) (Form1 E F)
    ((ContinuousLinearMap.compL ℝ E E F).flip L)).comp
      ((ContinuousLinearMap.compL ℝ E E (Form1 E F)).flip L)

theorem hessianPrecompositionCLM_apply (L : E →L[ℝ] E)
    (Q : Form2 E F) (a b : E) :
    hessianPrecompositionCLM L Q a b = Q (L a) (L b) := rfl

def postcomposeHessianCLM (B : Form2 E E) :
    (Form1 E F) →L[ℝ] Form2 E F :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (Form1 E F)).flip B).comp
    (ContinuousLinearMap.compL ℝ E E F)

theorem postcomposeHessianCLM_apply (B : Form2 E E)
    (p : Form1 E F) (a b : E) : postcomposeHessianCLM B p a b = p (B a b) := rfl

def gradientCorrectionCLM (L : E →L[ℝ] E) (K : Form2 E E) :
    (Form1 E F) →L[ℝ] Form2 E F :=
  - (postcomposeHessianCLM (hessianPrecompositionCLM L K)).comp
    ((ContinuousLinearMap.compL ℝ E E F).flip L)

theorem gradientCorrectionCLM_apply (L : E →L[ℝ] E) (K : Form2 E E)
    (p : Form1 E F) (a b : E) :
    gradientCorrectionCLM L K p a b = -p (L (K (L a) (L b))) := rfl

theorem hessianPrecompositionCLM_contDiff :
    ContDiff ℝ ∞ (fun L : E →L[ℝ] E => hessianPrecompositionCLM (F := F) L) := by
  have hinner : ContDiff ℝ ∞ (fun L : E →L[ℝ] E => (ContinuousLinearMap.compL ℝ E E F).flip L) :=
    ((ContinuousLinearMap.compL ℝ E E F).flip).contDiff
  have hpost : ContDiff ℝ ∞ (fun L : E →L[ℝ] E =>
      ContinuousLinearMap.compL ℝ E (Form1 E F) (Form1 E F)
        ((ContinuousLinearMap.compL ℝ E E F).flip L)) :=
    (ContinuousLinearMap.compL ℝ E (Form1 E F) (Form1 E F)).contDiff.comp hinner
  exact hpost.clm_comp ((ContinuousLinearMap.compL ℝ E E (Form1 E F)).flip).contDiff

theorem postcomposeHessianCLM_norm_le (B : Form2 E E) :
    ‖postcomposeHessianCLM (F := F) B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro p
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  change ‖p (B a b)‖ ≤ ‖B‖*‖p‖*‖a‖*‖b‖
  calc
    ‖p (B a b)‖ ≤ ‖p‖*‖B a b‖ := p.le_opNorm _
    _ ≤ ‖p‖*(‖B‖*‖a‖*‖b‖) := mul_le_mul_of_nonneg_left
      (((B a).le_opNorm b).trans (mul_le_mul_of_nonneg_right (B.le_opNorm a) (norm_nonneg b)))
        (norm_nonneg p)
    _ = _ := by ring

def postcomposeHessianLinearMap : Form2 E E →ₗ[ℝ] (Form1 E F →L[ℝ] Form2 E F) where
  toFun := postcomposeHessianCLM
  map_add' B C := by
    ext p a b
    simp only [postcomposeHessianCLM_apply,add_apply,map_add]
  map_smul' r B := by
    ext p a b
    simp only [postcomposeHessianCLM_apply,smul_apply,map_smul,RingHom.id_apply]

def postcomposeHessianOperator : Form2 E E →L[ℝ] (Form1 E F →L[ℝ] Form2 E F) :=
  (postcomposeHessianLinearMap (E := E) (F := F)).mkContinuous 1
    (fun B => by
      change ‖postcomposeHessianCLM (F := F) B‖ ≤ 1*‖B‖
      simpa only [one_mul] using postcomposeHessianCLM_norm_le (F := F) B)

theorem postcomposeHessianCLM_contDiff :
    ContDiff ℝ ∞ (fun B : Form2 E E => postcomposeHessianCLM (F := F) B) :=
  (postcomposeHessianOperator (E := E) (F := F)).contDiff

theorem gradientCorrectionCLM_contDiff :
    ContDiff ℝ ∞ (fun a : (E →L[ℝ] E) × (Form2 E E) =>
      gradientCorrectionCLM (F := F) a.1 a.2) := by
  have hpre : ContDiff ℝ ∞ (fun a : (E →L[ℝ] E) × (Form2 E E) =>
      hessianPrecompositionCLM (F := E) a.1) :=
    (hessianPrecompositionCLM_contDiff (E := E) (F := E)).comp contDiff_fst
  have hB := hpre.clm_apply (contDiff_snd)
  have hpost := (postcomposeHessianCLM_contDiff (E := E) (F := F)).comp hB
  exact (hpost.clm_comp (((ContinuousLinearMap.compL ℝ E E F).flip).contDiff.comp contDiff_fst)).neg

theorem hessianPrecompositionCLM_id :
    hessianPrecompositionCLM (F := F) (ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ (Form2 E F) := by
  ext Q a b
  rfl

theorem gradientCorrectionCLM_zero (L : E →L[ℝ] E) :
    gradientCorrectionCLM (F := F) L 0 = 0 := by
  ext p a b
  simp only [gradientCorrectionCLM_apply, zero_apply, map_zero, neg_zero]

end Yau.LeafProofs.L17BootstrapInverseHessianCoefficientsAux
