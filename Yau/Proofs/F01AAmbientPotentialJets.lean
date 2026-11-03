import Yau.Proofs.F01AAmbientPotentialSmooth
import Yau.Proofs.F01ALocalLeviLimit
import Yau.Proofs.F01ALocalInitialPotential
import Yau.Proofs.F01PotentialMetricAssembly
import Yau.Proofs.F01ChartLogDet

/-! Native closed-slab regularity on the genuine open manifold gives
the actual ambient potential jets at interior points. Their matrix and
clock in any original holomorphic chart are computed by its Jacobian. -/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem openExtendedPotential_inChart_contDiffAt
    (S : Opens M.Carrier) (hS : IsConnected (S : Set M.Carrier))
    (U : (openConnectedManifold M S hS).Carrier → ℝ → ℝ) {I : Set ℝ}
    (hU : SmoothSpaceTime U I)
    (x : (openConnectedManifold M S hS).Carrier) {t : ℝ} (ht : t ∈ I) :
    ContDiffAt ℝ ∞
      (inChart x.val (fun y => openExtendedPotential M S hS U y t))
      (chartPt x.val x.val) := by
  have hnative : ContDiffAt ℝ ∞ (inChart x (fun y => U y t)) (chartPt x x) :=
    ((smoothSpaceTime_slice hU ht) x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))
  have heq := openRestriction_inChart_eventuallyEq M S hS
    (fun y => openExtendedPotential M S hS U y t) x
  have hrestrict : (fun y : (openConnectedManifold M S hS).Carrier =>
      openExtendedPotential M S hS U y.val t) = fun y => U y t :=
    funext (fun y => openExtendedPotential_restrict M S hS U y t)
  rw [hrestrict] at heq
  exact hnative.congr_of_eventuallyEq heq.symm

theorem localNativePotentialMatrix_eq_native_congruence
    (g : HermitianField M) (hg : MetricSmooth g)
    (f : M.Carrier → ℝ → ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (t : ℝ)
    (hf : ContDiffAt ℝ 2 (inChart (e z) (fun y => f y t)) (chartPt (e z) (e z))) :
    localNativePotentialMatrix (pullbackMatrix g e) (fun p => f (e p.1) p.2) (z,t) =
      (linearMatrix (coordinateDifferential e (e z) z))ᴴ * nativePotentialMatrix g f t (e z) *
        linearMatrix (coordinateDifferential e (e z) z) := by
  have ha : e z ∈ (extChartAt (ComplexModel n) (e z)).source := mem_extChartAt_source (e z)
  have hG := pullbackMatrix_eq_congruence g e (e z) z ha
  have hR := pullbackRicci_eq_ricci g hg e he hei hz
  have hLevi := (local_holomorphic_chart_second_data (fun y => f y t) e he hz hf).2
  change pullbackMatrix g e z - (t : ℂ) • backgroundRicci (pullbackMatrix g e) z +
      leviC (fun w => f (e w) t) z = _
  change backgroundRicci (pullbackMatrix g e) z = _ at hR
  rw [hG, hR, hLevi]
  simp only [nativePotentialMatrix, gMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem localNativePotentialClock_eq_native_ratio
    (g : HermitianField M) (hg : MetricSmooth g)
    (f : M.Carrier → ℝ → ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (he : MDifferentiableOn (ComplexModel n) (ComplexModel n) e e.source)
    (hei : MDifferentiableOn (ComplexModel n) (ComplexModel n) e.symm e.target)
    {z : ComplexVector n} (hz : z ∈ e.source) (t : ℝ)
    (hf : ContDiffAt ℝ 2 (inChart (e z) (fun y => f y t)) (chartPt (e z) (e z)))
    (hpos : (nativePotentialMatrix g f t (e z)).PosDef) :
    localNativePotentialClock (pullbackMatrix g e) (fun p => f (e p.1) p.2) (z,t) =
      Real.log ((nativePotentialMatrix g f t (e z)).det.re / (gMat g (e z)).det.re) := by
  let J := linearMatrix (coordinateDifferential e (e z) z)
  have hJ : J.det ≠ 0 := linearMatrix_det_ne_zero _
    (coordinateDifferential_injective e he hei (e z) hz (mem_extChartAt_source (e z)))
  have hH := localNativePotentialMatrix_eq_native_congruence g hg f e he hei hz t hf
  have hG := pullbackMatrix_eq_congruence g e (e z) z (mem_extChartAt_source (e z))
  have hHdet : 0 <
      (localNativePotentialMatrix (pullbackMatrix g e) (fun p => f (e p.1) p.2) (z,t)).det.re := by
    rw [hH, congruence_det_re]
    exact mul_pos (Complex.normSq_pos.mpr hJ) (Complex.pos_iff.mp hpos.det_pos).1
  unfold localNativePotentialClock
  rw [← Real.log_div hHdet.ne' (pullbackMatrix_det_re_pos g e he hei hz).ne', hH, hG]
  exact congrArg Real.log (determinant_ratio_congruence _ _ J hJ)

end Yau.NodeProofs.F01Aux
