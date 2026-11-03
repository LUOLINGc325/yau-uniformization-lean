import Yau.LeafProofs.L17UniformJetCompact
import Yau.LeafProofs.L07

/-! All finite jets of the actual background coefficients and their inverses are uniform. -/

noncomputable section

open Set Metric
open scoped ContDiff Matrix ComplexOrder Matrix.Norms.Elementwise

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem BoundedChartFamily.pullbackMatrix_smooth (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => pullbackMatrix g (A.chart p) z) (ball 0 A.radius) :=
  contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => A.coefficient_smooth p i j

theorem BoundedChartFamily.coefficient_uniformJetBounds (A : BoundedChartFamily g)
    (k : ℕ) (a b : Fin n) :
    UniformJetBounds k (fun p z => pullbackMatrix g (A.chart p) z a b)
      (fun _ => ball 0 A.radius) := by
  apply UniformJetBounds.of_orderBounds
  intro j hj
  exact ⟨A.bound j, fun p z hz => A.coefficient_bound p j z hz a b⟩

theorem BoundedChartFamily.pullbackMatrix_uniformJetBounds (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p z => pullbackMatrix g (A.chart p) z)
      (fun _ => ball 0 A.radius) := by
  have hrow (a : Fin n) := UniformJetBounds.pi
    (fun b => A.coefficient_uniformJetBounds k a b) (fun _ => isOpen_ball)
    (fun b p => A.coefficient_smooth p a b)
  apply UniformJetBounds.pi hrow (fun _ => isOpen_ball)
  intro a p
  exact contDiffOn_pi.mpr fun b => A.coefficient_smooth p a b

theorem BoundedChartFamily.pullbackMatrix_norm_le (A : BoundedChartFamily g)
    (p : M.Carrier) {z : ComplexVector n} (hz : z ∈ ball 0 A.radius) :
    ‖pullbackMatrix g (A.chart p) z‖ ≤ A.bound 0 := by
  apply (pi_norm_le_iff_of_nonneg (A.bound_pos 0).le).mpr
  intro a
  apply (pi_norm_le_iff_of_nonneg (A.bound_pos 0).le).mpr
  intro b
  simpa only [norm_iteratedFDeriv_zero] using A.coefficient_bound p 0 z hz a b

theorem BoundedChartFamily.inverseMatrix_smooth (A : BoundedChartFamily g) (p : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => (pullbackMatrix g (A.chart p) z)⁻¹) (ball 0 A.radius) :=
  L07Aux.matrix_inv_contDiffOn _ (A.pullbackMatrix_smooth p) fun _z hz =>
    (pullbackMatrix_posDef g (A.chart p) (A.differentiable p) (A.inverse_differentiable p)
      (A.closedBall_source p (ball_subset_closedBall hz))).det_pos.ne'

theorem BoundedChartFamily.inverseMatrix_uniformJetBounds (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k (fun p z => (pullbackMatrix g (A.chart p) z)⁻¹)
      (fun _ => ball 0 A.radius) := by
  classical
  let C := A.bound 0
  let K : Set (Matrix (Fin n) (Fin n) ℂ) :=
    closedBall 0 C ∩ {H | (H - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef}
  let U : Set (Matrix (Fin n) (Fin n) ℂ) := {H | H.det ≠ 0}
  have hC : 0 < C := A.bound_pos 0
  have hclosed : IsClosed {H : Matrix (Fin n) (Fin n) ℂ |
      (H - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef} :=
    Matrix.posSemidef_is_closed.preimage (continuous_id.sub continuous_const)
  have hK : IsCompact K := (isCompact_closedBall (0 : Matrix (Fin n) (Fin n) ℂ) C).inter_right
    hclosed
  have hdet : Continuous (fun H : Matrix (Fin n) (Fin n) ℂ => H.det) := by fun_prop
  have hU : IsOpen U := isOpen_ne_fun hdet continuous_const
  have hKU : K ⊆ U := by
    intro H hH
    have hp : (((C⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (Complex.zero_lt_real.mpr (inv_pos.mpr hC))
    have hHpos : H.PosDef := by
      simpa only [add_sub_cancel] using hp.add_posSemidef hH.2
    exact hHpos.det_pos.ne'
  have hi : ContDiffOn ℝ ∞ (fun H : Matrix (Fin n) (Fin n) ℂ => H⁻¹) U :=
    L07Aux.matrix_inv_contDiffOn id contDiffOn_id (fun H hH => hH)
  obtain ⟨V, hVo, hKV, hVU, hVjets⟩ :=
    compact_buffer_uniformJetBounds (ι := M.Carrier) hK hU hKU hi
  have hmap (p : M.Carrier) : MapsTo (fun z => pullbackMatrix g (A.chart p) z)
      (ball 0 A.radius) V := by
    intro z hz
    apply hKV
    refine ⟨mem_closedBall.mpr ?_, ?_⟩
    · simpa only [dist_zero_right] using A.pullbackMatrix_norm_le p hz
    · change (pullbackMatrix g (A.chart p) z - ((C⁻¹ : ℝ) : ℂ) • 1).PosSemidef
      simpa only [C, Complex.ofReal_inv] using (A.comparison p z hz).1
  exact (A.pullbackMatrix_uniformJetBounds k).comp (hVjets k)
    (fun _ => isOpen_ball) (fun _ => hVo) (A.pullbackMatrix_smooth)
    (fun _ => hi.mono (subset_closure.trans hVU)) hmap

end Yau.LeafProofs.L17Aux
