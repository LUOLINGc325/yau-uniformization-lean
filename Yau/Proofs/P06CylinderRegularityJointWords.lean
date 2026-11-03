import Yau.Proofs.P06CylinderRegularityJointMaps
import Yau.LeafProofs.L16ParabolicCoordinates

/-! A fixed smooth coefficient map expresses each actual joint word of
χu in finitely many spatial jets of u. It is constructed before u. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.LeafProofs.L16Aux

variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

def jointJetDepth : List (ParabolicJointIdx n) → ℕ
  | [] => 0
  | _::w => jointJetDepth w + 2

theorem jointJetDepth_eq (w : List (ParabolicJointIdx n)) : jointJetDepth w = 2*w.length := by
  induction w with
  | nil => rfl
  | cons j w ih => simp only [jointJetDepth, ih, List.length_cons]; omega

def jetDirectionMap
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (s : ℕ) : ParabolicJointIdx n → Point n → JetSpace α n (s+2) →L[ℝ] JetSpace α n s
  | .inl i, _ => jetSpaceMap s i
  | .inr _, p => jetTimeMap q e1 e0 s p

def wordJetCLM
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (χ : Point n → ℝ) (r : α) :
    (w : List (ParabolicJointIdx n)) → Point n → JetSpace α n (jointJetDepth w) →L[ℝ] ℝ
  | [], p => χ p • ContinuousLinearMap.proj r
  | j::w, p =>
    (fderiv ℝ (wordJetCLM q e1 e0 χ r w) p (parabolicJointVec j)).comp (jetValueMap (jointJetDepth w)) +
      (wordJetCLM q e1 e0 χ r w p).comp (jetDirectionMap q e1 e0 (jointJetDepth w) j p)

theorem wordJetCLM_contDiff
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {χ : Point n → ℝ} (hχ : ContDiff ℝ ∞ χ) (r : α) (w : List (ParabolicJointIdx n)) :
    ContDiff ℝ ∞ (wordJetCLM q e1 e0 χ r w) := by
  induction w with
  | nil => exact hχ.smul contDiff_const
  | cons j w ih =>
    have hD : ContDiff ℝ ∞ (fun p => fderiv ℝ (wordJetCLM q e1 e0 χ r w) p
        (parabolicJointVec j)) :=
      (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hDir : ContDiff ℝ ∞ (jetDirectionMap q e1 e0 (jointJetDepth w) j) := by
      cases j with
      | inl i => exact contDiff_const
      | inr a => exact jetTimeMap_contDiff q e1 e0 hq hcq he1 hce1 he0 hce0 _
    exact (hD.clm_comp contDiff_const).add (ih.clm_comp hDir)

theorem jetDirectionMap_derivative
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    {Q : Set (Point n)} (hQ : IsOpen Q) (U : Point n → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r)) (hPDE : heatEquation q e1 e0 Q U)
    (s : ℕ) {p : Point n} (hp : p ∈ Q) (j : ParabolicJointIdx n) :
    fderiv ℝ (jetValue (fun i => (Yau.realVec i,0)) U s) p (parabolicJointVec j) =
      jetDirectionMap q e1 e0 s j p (jetValue (fun i => (Yau.realVec i,0)) U (s+2) p) := by
  cases j with
  | inl i => exact jetSpaceMap_derivative U hU s p i
  | inr a => exact jetTimeMap_derivative q e1 e0 hQ U hq hcq he1 hce1 he0 hce0 hU hPDE s hp

theorem wordJetCLM_actual
    (q : Yau.RIdx n → Yau.RIdx n → Point n → ℝ)
    (e1 : α → α → Yau.RIdx n → Point n → ℝ) (e0 : α → α → Point n → ℝ)
    {Q : Set (Point n)} (hQ : IsOpen Q) (U : Point n → α → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (hcq : ∀ i j, HasCompactSupport (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (hce1 : ∀ r c i, HasCompactSupport (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c)) (hce0 : ∀ r c, HasCompactSupport (e0 r c))
    {χ : Point n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hU : ∀ r, ContDiff ℝ ∞ (fun p => U p r)) (hPDE : heatEquation q e1 e0 Q U)
    (r : α) (w : List (ParabolicJointIdx n)) {p : Point n} (hp : p ∈ Q) :
    regularityCoefficientWord parabolicJointVec w (fun p => χ p * U p r) p =
      wordJetCLM q e1 e0 χ r w p
        (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w) p) := by
  induction w generalizing p with
  | nil => rfl
  | cons j w ih =>
    have hC := wordJetCLM_contDiff q e1 e0 hq hcq he1 hce1 he0 hce0 hχ r w
    have hV : ContDiff ℝ ∞ (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w)) :=
      contDiff_pi.mpr (jetValue_contDiff _ hU _)
    have hG : regularityCoefficientWord parabolicJointVec w (fun p => χ p * U p r) =ᶠ[𝓝 p]
        (fun z => wordJetCLM q e1 e0 χ r w z
          (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w) z)) := by
      filter_upwards [hQ.mem_nhds hp] with z hz
      exact ih hz
    have hDG : fderiv ℝ (regularityCoefficientWord parabolicJointVec w (fun p => χ p * U p r)) p =
        fderiv ℝ (fun z => wordJetCLM q e1 e0 χ r w z
          (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w) z)) p := hG.fderiv.eq_of_nhds
    change fderiv ℝ (regularityCoefficientWord parabolicJointVec w (fun p => χ p * U p r)) p
      (parabolicJointVec j) = _
    rw [hDG, fderiv_clm_apply (hC.differentiable (by simp) p) (hV.differentiable (by simp) p)]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [jetDirectionMap_derivative q e1 e0 hQ U hq hcq he1 hce1 he0 hce0 hU hPDE _ hp j]
    change _ = (fderiv ℝ (wordJetCLM q e1 e0 χ r w) p (parabolicJointVec j))
      (jetValueMap (jointJetDepth w) (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w+2) p)) +
      (wordJetCLM q e1 e0 χ r w p) (jetDirectionMap q e1 e0 (jointJetDepth w) j p
        (jetValue (fun i => (Yau.realVec i,0)) U (jointJetDepth w+2) p))
    rw [jetValueMap_apply]
    exact add_comm _ _

end Yau.NodeProofs.P06Aux.CylinderReg
