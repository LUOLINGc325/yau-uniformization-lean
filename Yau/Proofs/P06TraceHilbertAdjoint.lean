import Yau.Proofs.P06TraceHilbertMaps
import Yau.Proofs.P06HodgeEnergyPairings

noncomputable section
open MeasureTheory
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.TraceHilbert
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem scalarForm_inner (h : HermitianField M) (f q : M.Carrier → ℝ) (x : M.Carrier) :
    formInner h (scalarForm f) (scalarForm q) x = f x * q x := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  simp [formInner, scalarForm_components, inChart, hx]

theorem omega_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : M.Carrier → ℝ) (hf : L2RealForm g.form μ (scalarForm f)) :
    L2RealForm g.form μ (multiplyRealForm f (omegaForm g.form)) := by
  have hω := omegaForm_smooth g.form (L12Aux.metricSmooth_of_smoothMetric g)
  have hc : ∀ x (I : Fin 2 → RIdx n), AEStronglyMeasurable
      (fun y => multiplyRealForm f (omegaForm g.form) y
        (fun r => chartVec x y (realVec (I r))))
      (μ.restrict (chartAt (ComplexVector n) x).source) := by
    intro x I
    have hfm := hf.1 x Fin.elim0
    change AEStronglyMeasurable f (μ.restrict (chartAt (ComplexVector n) x).source) at hfm
    exact hfm.mul (smoothRealForm_coefficient_aestronglyMeasurable μ _ hω x I)
  have hi : Integrable (formNormSq g.form (multiplyRealForm f (omegaForm g.form))) μ := by
    have ht := (formNormSq_integrable g μ (scalarForm f) hf).mul_const (n : ℝ)
    change Integrable (fun x => formNormSq g.form (multiplyRealForm f (omegaForm g.form)) x) μ
    simpa only [multiplyRealForm_normSq, P06Weitzenbock.omegaForm_normSq,
      scalarForm_normSq] using ht
  exact ⟨hc, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun x => formNormSq_nonneg g.form _ x))).mp hi.2⟩

/-- The Hilbert adjoint is the actual pointwise multiplication by ω. -/
theorem omegaAdjoint_realize (g : SmoothMetric M) (μ : Measure M.Carrier)
    (f : M.Carrier → ℝ) (hf : L2RealForm g.form μ (scalarForm f)) :
    omegaAdjoint g μ (realizeActualForm g μ (scalarForm f) hf) =
      realizeActualForm g μ (multiplyRealForm f (omegaForm g.form)) (omega_l2 g μ f hf) := by
  apply ext_inner_left ℝ
  intro u
  obtain ⟨A, hA, heA⟩ := l2FormHilbert_exists_section g μ u
  change realizeActualForm g μ A hA = u at heA
  rw [← heA, omegaAdjoint_pairing, contraction_realize,
    realizeActualForm_inner, realizeActualForm_inner]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change formInner g.form (scalarForm (formInner g.form A (omegaForm g.form))) (scalarForm f) x = _
    rw [scalarForm_inner, multiplyRealForm_inner_right]
    exact mul_comm _ _

end Yau.NodeProofs.P06Aux.TraceHilbert
