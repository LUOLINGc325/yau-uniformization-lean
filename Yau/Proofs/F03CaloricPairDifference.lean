import Yau.Proofs.F03ClassicalCaloricWeakEquation
import Yau.Proofs.F03CaloricPairNorm

/-! Actual classical differences and exact subtraction of the L² value/gradient pair. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates LeafProofs.L16Aux
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

theorem classicalCaloricGradient_sub {D : Set (Point d)} (hD : IsOpen D)
    {u v : Point d → ℝ} (hu : ContDiffOn ℝ ∞ u D) (hv : ContDiffOn ℝ ∞ v D)
    {p : Point d} (hp : p ∈ D) (i : RIdx d) :
    classicalCaloricGradient (fun q => u q-v q) p i=
      classicalCaloricGradient u p i-classicalCaloricGradient v p i := by
  unfold classicalCaloricGradient
  rw [fderiv_fun_sub ((hu.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp))
    ((hv.contDiffAt (hD.mem_nhds hp)).differentiableAt (by simp))]
  rfl

theorem local_linearOp_sub {D : Set (Point d)} (hD : IsOpen D)
    (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
    {u v : Point d → ℝ} (hu : ContDiffOn ℝ ∞ u D) (hv : ContDiffOn ℝ ∞ v D)
    {p : Point d} (hp : p ∈ D) :
    linearOp D a b (fun q => u q-v q) p=linearOp D a b u p-linearOp D a b v p := by
  have hUS : ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1 :=
    ((hu.contDiffAt (hD.mem_nhds hp)).comp p.1 (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  have hVS : ContDiffAt ℝ 2 (fun x => v (x,p.2)) p.1 :=
    ((hv.contDiffAt (hD.mem_nhds hp)).comp p.1 (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  have hUT : DifferentiableAt ℝ (fun t => u (p.1,t)) p.2 :=
    ((hu.contDiffAt (hD.mem_nhds hp)).comp p.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hVT : DifferentiableAt ℝ (fun t => v (p.1,t)) p.2 :=
    ((hv.contDiffAt (hD.mem_nhds hp)).comp p.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hS : spatialD (fun q => u q-v q) p=spatialD u p-spatialD v p :=
    fderiv_fun_sub (hUS.differentiableAt (by norm_num)) (hVS.differentiableAt (by norm_num))
  have hSS : spatialDD (fun q => u q-v q) p=spatialDD u p-spatialDD v p := secondFDeriv_sub hUS hVS
  simp only [linearOp,timeD_eq_deriv_of_isOpen hD hp,deriv_fun_sub hUT hVT,hS,hSS,
    ContinuousLinearMap.sub_apply,mul_sub,Finset.sum_sub_distrib]
  ring

theorem caloric_pair_sub_norm {D : Set (Point d)} (u v : Point d → ℝ)
    (G H : Point d → RIdx d → ℝ)
    (hu : MemLp u 2 (volume.restrict D)) (hv : MemLp v 2 (volume.restrict D))
    (hG : ∀ i, MemLp (fun p => G p i) 2 (volume.restrict D))
    (hH : ∀ i, MemLp (fun p => H p i) 2 (volume.restrict D)) :
    ‖((hu.toLp u,fun i => (hG i).toLp (fun p => G p i)) : CaloricAmbient D)-
      (hv.toLp v,fun i => (hH i).toLp (fun p => H p i))‖=
      ‖(((hu.sub hv).toLp (fun p => u p-v p),
        fun i => ((hG i).sub (hH i)).toLp (fun p => G p i-H p i)) : CaloricAmbient D)‖ := by
  congr 1

end Yau.Proofs.F03Aux
