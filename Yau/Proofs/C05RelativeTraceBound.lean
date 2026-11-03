import Yau.Proofs.C05UnitaryFrame
import Yau.Proofs.C05PositiveTrace
import Yau.Proofs.C05HarnackMinimum
import Yau.Proofs.C05ScalarGradientNorm

/-! The actual scalar trace bounds Ricci relative to the same metric.
Consequently the scalar Harnack inequality bounds the metric gradient. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder Manifold Topology ContDiff
namespace Yau.Proofs.C05Aux
open Yau Matrix Yau.Proofs.C05UnitaryFrameAux Yau.LeafProofs.L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem relative_positive_matrix_le_trace (g A : Matrix (Fin n) (Fin n) ℂ)
    (hg : g.PosDef) (hA : A.PosDef) :
    ((((g⁻¹ * A).trace).re : ℂ) • g - A).PosSemidef := by
  obtain ⟨W,lam,hdet,hGram,hdiag,hpos,htr⟩ := unitary_frame_exists g A hg hA
  have hM : (Wᴴ * A * W).PosSemidef := hA.posSemidef.conjTranspose_mul_mul_same W
  have htrace : (Wᴴ * A * W).trace.re = (g⁻¹ * A).trace.re := by
    rw [hdiag,Matrix.trace_diagonal]
    change Complex.reCLM (∑ j, (lam j : ℂ)) = _
    rw [map_sum]
    simpa only [Complex.reCLM_apply,Complex.ofReal_re] using htr
  have hp := positive_matrix_le_trace _ hM
  rw [htrace] at hp
  have he : Wᴴ * ((((g⁻¹*A).trace).re : ℂ) • g - A) * W =
      (((g⁻¹*A).trace).re : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Wᴴ*A*W := by
    simp only [Matrix.mul_sub,Matrix.sub_mul,Matrix.smul_mul,Matrix.mul_smul,hGram]
  have hu : IsUnit W := (Matrix.isUnit_iff_isUnit_det W).mpr (isUnit_iff_ne_zero.mpr hdet)
  apply hu.posSemidef_star_left_conjugate_iff.mp
  change (Wᴴ * _ * W).PosSemidef
  rw [he]
  exact hp

theorem metric_dual_le_harnack_of_trace_one (g A : Matrix (Fin n) (Fin n) ℂ)
    (hg : g.PosDef) (hA : A.PosDef) (htrace : (g⁻¹ * A).trace.re = 1)
    (p : ComplexVector n) (S : ℝ)
    (hH : ∀ v : Fin n → ℂ,
      0 ≤ S + 2 * (∑ i, v i * p i).re + (star v ⬝ᵥ (A *ᵥ v)).re) :
    dualNormMat g p ≤ S := by
  have hdiff := relative_positive_matrix_le_trace g A hg hA
  rw [htrace] at hdiff
  simp only [Complex.ofReal_one,one_smul] at hdiff
  apply (scalar_harnack_minimum g hg p S _).2
  intro v
  have hv := (Complex.nonneg_iff.mp (hdiff.dotProduct_mulVec_nonneg v)).1
  simp only [Matrix.sub_mulVec,dotProduct_sub,Complex.sub_re] at hv
  linarith [hH v]

theorem scalarJetNorm_one_sq_eq_twice_gradNormSq (k : HermitianField M)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) :
    scalarJetNorm k f 1 x ^ 2 = 2 * gradNormSq k f x := by
  have hG := Yau.LeafProofs.L12Aux.realMetricFn_posDef k x (chartPt x x) (mem_extChartAt_target x)
  rw [scalarJetNorm,Real.sq_sqrt (Yau.LeafProofs.L23Aux.covTensorNormSq_nonneg _ hG _),
    scalarJet_one_normSq]
  have he := scalarGradientPair_eq_twice_gradNormSq k hf x
  change scalarGradientPair k f f x = _ at he
  rw [scalarGradientPair,chartGradientPair_eq_sum] at he
  exact he

end Yau.Proofs.C05Aux
