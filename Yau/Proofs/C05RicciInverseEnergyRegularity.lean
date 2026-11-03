import Yau.Proofs.C05RicciInverseEnergyChart
import Yau.Proofs.C05InverseFieldJets
import Yau.LeafProofs.L23MetricMixedTime

/-! Smoothness of the actual inverse Ricci energy in every fixed chart.
Its inverse is the inverse of the actual Ricci form. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem realRicciMatrix_posDef_inChart (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (hA : ∀ x, (ricci k x).PosDef) (c : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    (Matrix.of (realRicciCoeff k c z)).PosDef := by
  let d := chartInv c z
  let J := realChartJacobian c d z
  have hJdet : J.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse
    (realChartJacobian_left_inverse c d hz (mem_extChartAt_source d))
  have hJu : IsUnit J := (Matrix.isUnit_iff_isUnit_det J).mpr
    (isUnit_iff_ne_zero.mpr hJdet)
  have hP := (realRicciMatrix_posDef k hk hK d (hA d)).conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hJu)
  rw [realRicciMatrix_chart_change k hk c d hz (mem_extChartAt_source d)]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,J,d,realChartChange] using hP

theorem ricciInverseTensor_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (hA : ∀ x, (ricci k x).PosDef) (c : M.Carrier)
    (v : Fin 2 → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => ricciInverseTensor k c z v) (chartTarget c) := by
  exact inverseFieldJet_zero_contDiffOn k hk c (fun z => Matrix.of (realRicciCoeff k c z))
    (realRicciCoeff_contDiffOn k hk c)
    (fun z hz => (realRicciMatrix_posDef_inChart k hk hK hA c hz).det_pos.ne') v

theorem ricciInverseEnergyInChart_contDiffOn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (hA : ∀ x, (ricci k x).PosDef)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) (c : M.Carrier) :
    ContDiffOn ℝ ∞ (ricciInverseEnergyInChart k f c) (chartTarget c) := by
  have hp (a : RIdx n) := rDeriv_contDiffOn
    (isOpen_extChartAt_target (I := ComplexModel n) c) (hf c) a
  have hi := Yau.LeafProofs.L12Aux.contDiffOn_matrix_inv
    (realRicciCoeff_contDiffOn k hk c)
    (fun z hz => (realRicciMatrix_posDef_inChart k hk hK hA c hz).det_pos.ne')
  unfold ricciInverseEnergyInChart realDifferentialInChart
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact contDiffOn_const.mul ((hp a).mul ((hi a b).mul (hp b)))

theorem realRicciDifferentialEnergy_smoothFn (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (hA : ∀ x, (ricci k x).PosDef)
    (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    SmoothFn (realRicciDifferentialEnergy k f) := by
  intro c
  exact (ricciInverseEnergyInChart_contDiffOn k hk hK hA f hf c).congr
    (fun z hz => (ricciInverseEnergyInChart_eq_global k hk f hf c hz).symm)

end Yau.Proofs.C05Aux
