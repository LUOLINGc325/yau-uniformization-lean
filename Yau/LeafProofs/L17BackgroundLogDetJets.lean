import Yau.LeafProofs.L17CoefficientJets
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def BoundedChartFamily.backgroundLogDet (A : BoundedChartFamily g)
    (p : M.Carrier) (z : ComplexVector n) : ℝ :=
  Real.log ((pullbackMatrix g (A.chart p) z).det.re)

theorem backgroundLogDetMatrix_smooth :
    ContDiffOn ℝ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => Real.log H.det.re)
      {H | 0 < H.det.re} := by
  have hd : ContDiffOn ℝ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => H.det)
      {H | 0 < H.det.re} := L07Aux.matrix_determinant_contDiffOn
    (fun H : Matrix (Fin n) (Fin n) ℂ => H) contDiffOn_id
  have hre := Complex.reCLM.contDiff.comp_contDiffOn hd
  exact hre.log (fun H hH => (hH : 0 < H.det.re).ne')

theorem BoundedChartFamily.backgroundLogDet_det_pos (A : BoundedChartFamily g)
    (p : M.Carrier) {z : ComplexVector n} (hz : z ∈ ball 0 A.radius) :
    0 < (pullbackMatrix g (A.chart p) z).det.re := by
  have hp := pullbackMatrix_posDef g (A.chart p) (A.differentiable p)
    (A.inverse_differentiable p) (A.closedBall_source p (ball_subset_closedBall hz))
  exact (Complex.pos_iff.mp hp.det_pos).1

theorem BoundedChartFamily.backgroundLogDet_smooth (A : BoundedChartFamily g)
    (p : M.Carrier) :
    ContDiffOn ℝ ∞ (A.backgroundLogDet p) (ball 0 A.radius) := by
  exact backgroundLogDetMatrix_smooth.comp (A.pullbackMatrix_smooth p)
    (fun z hz => A.backgroundLogDet_det_pos p hz)

theorem BoundedChartFamily.backgroundLogDet_uniformJetBounds
    (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (A.backgroundLogDet) (fun _ => ball 0 A.radius) := by
  classical
  let C := A.bound 0
  let K : Set (Matrix (Fin n) (Fin n) ℂ) :=
    closedBall 0 C ∩ {H | (H - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef}
  let U : Set (Matrix (Fin n) (Fin n) ℂ) := {H | 0 < H.det.re}
  have hC : 0 < C := A.bound_pos 0
  have hclosed : IsClosed {H : Matrix (Fin n) (Fin n) ℂ |
      (H - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)
  have hK : IsCompact K := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) C).inter_right hclosed
  have hdetre : Continuous (fun H : Matrix (Fin n) (Fin n) ℂ => H.det.re) := by fun_prop
  have hU : IsOpen U := isOpen_lt continuous_const hdetre
  have hKU : K ⊆ U := by
    intro H hH
    have hp : (((C⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr (inv_pos.mpr hC))
    have hHpos : H.PosDef := by
      simpa only [add_sub_cancel] using hp.add_posSemidef hH.2
    exact (Complex.pos_iff.mp hHpos.det_pos).1
  have hpsi : ContDiffOn ℝ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => Real.log H.det.re) U :=
    backgroundLogDetMatrix_smooth
  obtain ⟨V,hVo,hKV,hVU,hVjets⟩ :=
    compact_buffer_uniformJetBounds (ι := M.Carrier) hK hU hKU hpsi
  have hmap (p : M.Carrier) : MapsTo (fun z => pullbackMatrix g (A.chart p) z)
      (ball 0 A.radius) V := by
    intro z hz
    apply hKV
    refine ⟨mem_closedBall.mpr ?_,?_⟩
    · simpa only [dist_zero_right] using A.pullbackMatrix_norm_le p hz
    · change (pullbackMatrix g (A.chart p) z - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef
      simpa only [C,Complex.ofReal_inv] using (A.comparison p z hz).1
  exact (A.pullbackMatrix_uniformJetBounds k).comp (hVjets k)
    (fun _ => isOpen_ball) (fun _ => hVo) A.pullbackMatrix_smooth
    (fun _ => hpsi.mono (subset_closure.trans hVU)) hmap

theorem BoundedChartFamily.backgroundLogDet_fderiv_smooth (A : BoundedChartFamily g)
    (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fderiv ℝ (A.backgroundLogDet p)) (ball 0 A.radius) :=
  (A.backgroundLogDet_smooth p).fderiv_of_isOpen isOpen_ball (by simp)

theorem BoundedChartFamily.backgroundLogDet_hessian_smooth (A : BoundedChartFamily g)
    (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) z)
      (ball 0 A.radius) :=
  (A.backgroundLogDet_fderiv_smooth p).fderiv_of_isOpen isOpen_ball (by simp)

theorem BoundedChartFamily.backgroundLogDet_fderiv_uniformJetBounds
    (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p => fderiv ℝ (A.backgroundLogDet p))
      (fun _ => ball 0 A.radius) :=
  (A.backgroundLogDet_uniformJetBounds (k+1)).fderiv

theorem BoundedChartFamily.backgroundLogDet_hessian_uniformJetBounds
    (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p z => fderiv ℝ (fderiv ℝ (A.backgroundLogDet p)) z)
      (fun _ => ball 0 A.radius) :=
  ((A.backgroundLogDet_uniformJetBounds (k+1+1)).fderiv).fderiv

end Yau.LeafProofs.L17Aux
