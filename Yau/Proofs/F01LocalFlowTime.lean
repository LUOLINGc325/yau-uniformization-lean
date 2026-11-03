import Yau.Proofs.F01SpaceTimeChart
import Yau.Proofs.F01PotentialChartIdentity
import Yau.Proofs.F01LocalPotentialEvolution

/-! The original scalar potential equation supplies the actual metric
time jet in every fixed holomorphic chart. This uses its actual potential
and determinant ratio, with no independent metric evolution assumption. -/
noncomputable section
open Set
open scoped Manifold ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def localSpaceTimePotential (α : HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (e : ComplexVector n → M.Carrier) (p : ComplexVector n × ℝ) : ℝ :=
  U (e p.1) p.2 + p.2 * Real.log (pullbackMatrix α e p.1).det.re

theorem localSpaceTimePotential_contDiffOn (α : HermitianField M) (hα : MetricSmooth α)
    (U : M.Carrier → ℝ → ℝ) {I : Set ℝ} (hU : SmoothSpaceTime U I)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target) :
    ContDiffOn ℝ ∞ (localSpaceTimePotential α U e) (e.source ×ˢ I) :=
  (smoothSpaceTime_holomorphic_chart hU e he).add
    (contDiffOn_snd.mul ((pullback_logdet_contDiffOn α hα e he hei).comp
      contDiffOn_fst (fun _ hp => hp.1)))

theorem localSpaceTimePotential_hasDerivAt (α : HermitianField M)
    (U : M.Carrier → ℝ → ℝ) (h : ℝ → HermitianField M)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) {t : ℝ}
    (hU : HasDerivAt (U (e z))
      (Real.log ((gMat (h t) (e z)).det.re / (gMat α (e z)).det.re)) t) :
    HasDerivAt (fun s => localSpaceTimePotential α U e (z, s))
      (Real.log (pullbackMatrix (h t) e z).det.re) t := by
  have hratio := pullbackMatrix_determinant_ratio (h t) α e he hei (e z) hz (mem_extChartAt_source (e z))
  change (pullbackMatrix (h t) e z).det.re / (pullbackMatrix α e z).det.re =
    (gMat (h t) (e z)).det.re / (gMat α (e z)).det.re at hratio
  have hp : 0 < (pullbackMatrix (h t) e z).det.re :=
    (Complex.pos_iff.mp (pullbackMatrix_posDef (h t) e he hei hz).det_pos).1
  have hαp : 0 < (pullbackMatrix α e z).det.re :=
    (Complex.pos_iff.mp (pullbackMatrix_posDef α e he hei hz).det_pos).1
  have hlog : Real.log ((gMat (h t) (e z)).det.re / (gMat α (e z)).det.re) =
      Real.log (pullbackMatrix (h t) e z).det.re - Real.log (pullbackMatrix α e z).det.re := by
    rw [← hratio, Real.log_div hp.ne' hαp.ne']
  have hlinear : HasDerivAt (fun s : ℝ => s * Real.log (pullbackMatrix α e z).det.re)
      (Real.log (pullbackMatrix α e z).det.re) t := by
    convert (hasDerivAt_id t).mul_const (Real.log (pullbackMatrix α e z).det.re) using 1 <;>
      first | rfl | simp
  have hh := hU.add hlinear
  rw [hlog] at hh
  convert hh using 1 <;> first | rfl | ring

theorem flow_potential_chart_matrix_hasDerivAt
    (α : HermitianField M) (hα : MetricSmooth α)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    {I : Set ℝ} (hI : IsOpen I) (hU : SmoothSpaceTime U I)
    (hpot : ∀ s ∈ I, ∀ x, gMat (h s) x = gMat α x - (s : ℂ) • ricci α x + levi (fun y => U y s) x)
    (hpde : ∀ x s, s ∈ I → HasDerivAt (U x)
      (Real.log ((gMat (h s) x).det.re / (gMat α x).det.re)) s)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) {t : ℝ} (ht : t ∈ I) (i j : Fin n) :
    HasDerivAt (fun s => pullbackMatrix (h s) e z i j)
      (leviC (fun w => Real.log (pullbackMatrix (h t) e w).det.re) z i j) t := by
  apply local_potential_matrix_hasDerivAt (pullbackMatrix α e)
    (fun p => pullbackMatrix (h p.2) e p.1) (localSpaceTimePotential α U e)
    e.open_source hI (localSpaceTimePotential_contDiffOn α hα U hU e he hei)
    (fun y hy s hs => ?_) (fun y hy s hs => ?_) hz ht i j
  · have hidentity := metric_potential_identity_in_chart α (h s) hα (fun x => U x s)
      (smoothSpaceTime_slice hU hs) s (hpot s hs) e he hei hy
    change pullbackMatrix (h s) e y = pullbackMatrix α e y +
      leviC (localFlowPotential α (fun x => U x s) s e) y
    rw [← hidentity]
    abel
  · exact localSpaceTimePotential_hasDerivAt α U h e he hei hy (hpde (e y) s hs)

end Yau.NodeProofs.F01Aux
