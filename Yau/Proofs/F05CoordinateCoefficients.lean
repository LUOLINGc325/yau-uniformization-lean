import Yau.Proofs.F05ChartRegularity
import Yau.Proofs.F05AtlasHomeomorph

/-! The exact flattened principal coefficient and drift coincide with the
native nonlinear chart calculus, including the full second-chart-derivative drift. -/

open Set
open scoped Topology ContDiff Manifold Matrix
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.Proofs.F05Aux

open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_trace_levi_baseA (h : HermitianField M) (x : M.Carrier)
    {z : Space n} (hz : z ∈ chartTarget x) {f : Space n → ℝ}
    (hf : ContDiffAt ℝ 2 f z) :
    traceWith (hMat h x z) (leviC f z) =
      ∑ a, ∑ b, baseA h x z a b * fderiv ℝ (fderiv ℝ f) z (realVec a) (realVec b) := by
  rw [traceWith_levi_eq_scalarSymbol _ hf,← F05_baseA_eq_scalarSymbol h x hz]
  rfl

theorem F05_coord_comp_fderiv {F : Space n → Space n} {x : Space n}
    (hF : DifferentiableAt ℝ F x) (a : RIdx n) :
    fderiv ℝ (fun w => realCoord (F w) a) x = (realCoordLinear a).comp (fderiv ℝ F x) := by
  have heq : (fun w => realCoord (F w) a) = (realCoordLinear a) ∘ F := by
    funext w
    exact (realCoordLinear_apply a (F w)).symm
  rw [heq,fderiv_comp x (realCoordLinear a).differentiableAt hF,
    ContinuousLinearMap.fderiv]

theorem F05_coord_comp_secondFDeriv {F : Space n → Space n} {x : Space n}
    (hF : ContDiffAt ℝ 2 F x) (a : RIdx n) (v w : Space n) :
    fderiv ℝ (fderiv ℝ (fun y => realCoord (F y) a)) x v w =
      realCoord (fderiv ℝ (fderiv ℝ F) x v w) a := by
  rw [secondFDeriv_chart_comp hF ((F05_realCoord_contDiff a).contDiffAt.of_le (by simp))]
  simp only [chartSecondJet_apply,F05_realCoord_secondFDeriv,F05_realCoord_fderiv,
    zero_apply,zero_add,realCoordLinear_apply]

theorem F05_flatA_chartPrincipal {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : HermitianField M) (i : Fin A.count)
    (p : Point n) (hp : p.1 ∈ Metric.ball 0 3) :
    flatA h A i p = chartPrincipalMatrix (fderiv ℝ (A.forward i) (A.inverse i p.1))
      (baseA h (A.center i) (A.inverse i p.1)) := by
  have hx := (hA.1 i).2.2.2.2.1 ⟨p.1,hp,rfl⟩
  have hF : DifferentiableAt ℝ (A.forward i) (A.inverse i p.1) :=
    (((hA.1 i).2.2.1).contDiffAt ((hA.1 i).1.mem_nhds hx)).differentiableAt (by simp)
  funext a b
  unfold flatA chartPrincipalMatrix
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  change _ * fderiv ℝ (fun w => realCoord (A.forward i w) a) (A.inverse i p.1) (realVec c) *
    fderiv ℝ (fun w => realCoord (A.forward i w) b) (A.inverse i p.1) (realVec e) = _
  rw [F05_coord_comp_fderiv hF a,F05_coord_comp_fderiv hF b]
  simp only [ContinuousLinearMap.comp_apply,realCoordLinear_apply]

theorem F05_flatB_chartDrift {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : HermitianField M) (i : Fin A.count)
    (p : Point n) (hp : p.1 ∈ Metric.ball 0 3) :
    flatB h A i p = chartDriftVector (fderiv ℝ (A.forward i) (A.inverse i p.1))
      (fderiv ℝ (fderiv ℝ (A.forward i)) (A.inverse i p.1))
      (baseA h (A.center i) (A.inverse i p.1)) (fun _ => 0) := by
  have hx := (hA.1 i).2.2.2.2.1 ⟨p.1,hp,rfl⟩
  have hxt := (hA.1 i).2.1 hx
  have hF : ContDiffAt ℝ 2 (A.forward i) (A.inverse i p.1) :=
    (((hA.1 i).2.2.1).contDiffAt ((hA.1 i).1.mem_nhds hx)).of_le (by simp)
  funext a
  have hc : ContDiffAt ℝ 2 (fun w => realCoord (A.forward i w) a) (A.inverse i p.1) :=
    ((F05_realCoord_contDiff a).contDiffAt.of_le (by simp)).comp _ hF
  unfold flatB
  rw [F05_trace_levi_baseA h (A.center i) hxt hc]
  simp only [F05_coord_comp_secondFDeriv hF,chartDriftVector,zero_mul,
    Finset.sum_const_zero,add_zero]

end Yau.Proofs.F05Aux
