import Yau.Proofs.F05JetComponents
import Yau.Proofs.F05BCFExtension
import Yau.Proofs.F05CutoffContinuity
import Yau.Proofs.F05FlatRegions

/-! Inner cutoffs extend all four continuous physical jet components through
the artificial chart rim. The true physical boundary remains one-sided. -/

open Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

local instance f05_cutoffDualGroup : NormedAddCommGroup (F05Dual n) := inferInstance
local instance f05_cutoffDualSpace : NormedSpace ℝ (F05Dual n) := inferInstance
local instance f05_cutoffHessianGroup : NormedAddCommGroup (F05Hessian n) := f05_jetHessianGroup
local instance f05_cutoffHessianSpace : NormedSpace ℝ (F05Hessian n) := f05_jetHessianSpace

theorem F05_model_cutoff_continuousOn {E F G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    (A : AtlasData M) (i : Fin A.count) (T : ℝ) (B : E → F → G)
    (hB : Continuous (fun p : E × F => B p.1 p.2)) (hZero : ∀ y, B 0 y = 0)
    (a : Space n → E) (ha : Continuous a) (hSupport : tsupport a ⊆ Metric.closedBall 0 1)
    (f : BoundedContinuousFunction (F05Q A i T) F) :
    ContinuousOn (fun p => B (a p.1) (F05BCFFun f p))
      (cylinder (closure (F05ModelOpen A i)) 0 T) := by
  let U : Set (Point n) := {p | p.1 ∈ Metric.ball 0 2}
  have hU : IsOpen U := Metric.isOpen_ball.preimage continuous_fst
  have hSub : U ∩ cylinder (closure (F05ModelOpen A i)) 0 T ⊆ F05Q A i T := by
    intro p hp
    have hpU : p.1 ∈ Metric.ball (0 : Space n) 2 := hp.1
    have hn : ‖p.1‖ < 2 := by simpa only [Metric.mem_ball,dist_zero_right] using hpU
    have hFace := hp.2.1
    rw [F05ModelOpen_eq,F05FlatOpen_closure] at hFace
    exact ⟨⟨hn.le,hFace⟩,hp.2.2⟩
  have hS : tsupport (fun p : Point n => a p.1) ⊆ U := by
    intro p hp
    have hpa : p.1 ∈ tsupport a := tsupport_comp_subset_preimage a continuous_fst hp
    have hn := hSupport hpa
    exact (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)) hn
  exact F05_continuousOn_cutoff_operation hU B hB hZero (ha.comp continuous_fst)
    ((F05BCFFun_continuousOn f).mono hSub) hS

def F05CutoffJetValue {α : ℝ} {Q : Set (Point n)}
    (φ : Space n → ℝ) (u : F05JetComponent α Q) (p : Point n) : ℝ :=
  φ p.1 * F05BCFFun u.1 p

def F05CutoffJetGradient {α : ℝ} {Q : Set (Point n)}
    (φ : Space n → ℝ) (u : F05JetComponent α Q) (p : Point n) : F05Dual n :=
  φ p.1 • F05BCFFun u.2.1 p + F05BCFFun u.1 p • fderiv ℝ φ p.1

def F05CutoffJetHessian {α : ℝ} {Q : Set (Point n)}
    (φ : Space n → ℝ) (u : F05JetComponent α Q) (p : Point n) : F05Hessian n :=
  φ p.1 • F05BCFFun u.2.2.1.val.1 p +
    (fderiv ℝ φ p.1).smulRight (F05BCFFun u.2.1 p) +
    (F05BCFFun u.2.1 p).smulRight (fderiv ℝ φ p.1) +
    F05BCFFun u.1 p • fderiv ℝ (fderiv ℝ φ) p.1

def F05CutoffJetTime {α : ℝ} {Q : Set (Point n)}
    (φ : Space n → ℝ) (u : F05JetComponent α Q) (p : Point n) : ℝ :=
  φ p.1 * F05BCFFun u.2.2.2.val.1 p

theorem F05_cutoff_jet_continuousOn (A : AtlasData M) (i : Fin A.count) (α T : ℝ)
    (φ : Space n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hSupport : tsupport φ ⊆ Metric.closedBall 0 1) (u : F05JetComponent α (F05Q A i T)) :
    ContinuousOn (F05CutoffJetValue φ u) (cylinder (closure (F05ModelOpen A i)) 0 T) ∧
    ContinuousOn (F05CutoffJetGradient φ u) (cylinder (closure (F05ModelOpen A i)) 0 T) ∧
    ContinuousOn (F05CutoffJetHessian φ u) (cylinder (closure (F05ModelOpen A i)) 0 T) ∧
    ContinuousOn (F05CutoffJetTime φ u) (cylinder (closure (F05ModelOpen A i)) 0 T) := by
  have hφD : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  have hφDD : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ φ)) := hφD.fderiv_right (by simp)
  have hDS : tsupport (fderiv ℝ φ) ⊆ Metric.closedBall 0 1 :=
    (tsupport_fderiv_subset ℝ).trans hSupport
  have hDDS : tsupport (fderiv ℝ (fderiv ℝ φ)) ⊆ Metric.closedBall 0 1 :=
    (tsupport_fderiv_subset ℝ).trans hDS
  have hV := F05_model_cutoff_continuousOn A i T (fun a v : ℝ => a*v)
    (by fun_prop) (by intro v; exact zero_mul v) φ hφ.continuous hSupport u.1
  have hG := F05_model_cutoff_continuousOn A i T (fun (a : ℝ) (v : F05Dual n) => a • v)
    (by fun_prop) (by intro v; exact zero_smul ℝ v) φ hφ.continuous hSupport u.2.1
  have hVG := F05_model_cutoff_continuousOn A i T (fun (a : F05Dual n) (v : ℝ) => v • a)
    (by fun_prop) (by intro v; exact smul_zero v) (fderiv ℝ φ) hφD.continuous hDS u.1
  have hH := F05_model_cutoff_continuousOn A i T (fun (a : ℝ) (v : F05Hessian n) => a • v)
    (by fun_prop) (by intro v; exact zero_smul ℝ v) φ hφ.continuous hSupport u.2.2.1.val.1
  have hGH := F05_model_cutoff_continuousOn A i T
    (fun (a v : F05Dual n) => a.smulRight v) (by fun_prop) (by intro v; ext x y; simp)
    (fderiv ℝ φ) hφD.continuous hDS u.2.1
  have hHG := F05_model_cutoff_continuousOn A i T
    (fun (a v : F05Dual n) => v.smulRight a) (by fun_prop) (by intro v; ext x y; simp)
    (fderiv ℝ φ) hφD.continuous hDS u.2.1
  have hVH := F05_model_cutoff_continuousOn A i T (fun (a : F05Hessian n) (v : ℝ) => v • a)
    (by fun_prop) (by intro v; exact smul_zero v) (fderiv ℝ (fderiv ℝ φ)) hφDD.continuous hDDS u.1
  have hTime := F05_model_cutoff_continuousOn A i T (fun a v : ℝ => a*v)
    (by fun_prop) (by intro v; exact zero_mul v) φ hφ.continuous hSupport u.2.2.2.val.1
  exact ⟨hV,hG.add hVG,((hH.add hGH).add hHG).add hVH,hTime⟩

end Yau.Proofs.F05Aux
