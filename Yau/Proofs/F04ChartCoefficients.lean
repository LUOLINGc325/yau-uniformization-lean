import Yau.Proofs.F04Source
import Yau.Proofs.F04AuxiliaryMatrix

open Filter Set
open scoped Topology ContDiff Manifold Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.F04Proof

open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L18Aux

theorem matrix_contDiffOn_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {s : Set E} {A : E → Mat n}
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun p => A p i j) s) : ContDiffOn ℝ ∞ A s := by
  classical
  have he (i j : RIdx n) : ContDiffOn ℝ ∞
      (fun p => (A p i j) • (Matrix.single i j (1 : ℝ) : Mat n)) s :=
    (hA i j).smul contDiffOn_const
  have hs := ContDiffOn.sum (s := Finset.univ) (fun i _ =>
    ContDiffOn.sum (s := Finset.univ) (fun j _ => he i j))
  convert hs using 1
  funext p
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, ite_and]
  simp

def flowChartPrincipal {n : ℕ} {M : ComplexManifold n} (h : ℝ → HermitianField M)
    (x : M.Carrier) (p : Point n) : Mat n :=
  fun i j => (1 / 2 : ℝ) * (realMetricFn (h p.2) x p.1)⁻¹ i j

theorem flowChartPrincipal_smooth {n : ℕ} {M : ComplexManifold n}
    (h : ℝ → HermitianField M) {I : Set ℝ} (hh : MetricFamilySmooth h I) (x : M.Carrier) :
    SmoothCoefficients (chartTarget x ×ˢ I) (flowChartPrincipal h x) (fun _ _ => 0) := by
  refine ⟨matrix_contDiffOn_of_entries ?_, fun _ => contDiffOn_const⟩
  intro i j
  exact contDiffOn_const.mul (contDiffOn_matrix_inv (hh x)
    (fun p hp => (LeafProofs.L12Aux.realMetricFn_posDef (h p.2) x p.1 hp.1).det_pos.ne') i j)

/-- The coefficient field is computed from the actual supplied Hermitian family;
its operator is the original complex Laplacian in every physical chart. -/
theorem flowChartPrincipal_operator {n : ℕ} {M : ComplexManifold n}
    (h : ℝ → HermitianField M) (x : M.Carrier) {v : M.Carrier → ℝ} (hv : SmoothFn v)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (t : ℝ) :
    laplacian (h t) v (chartInv x z) =
      ∑ i, ∑ j, flowChartPrincipal h x (z, t) i j *
        spatialDD (fun p : Point n => v (chartInv x p.1)) (z, t) (realVec i) (realVec j) := by
  have hf : ContDiffAt ℝ 2 (inChart x v) z :=
    ((hv x).contDiffAt ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  have hh := principal_realLaplacian_eq_twice_traceWith (h t) x hz hf
  rw [traceWith_inChart_eq_laplacian (h t) hv x hz] at hh
  change laplacian (h t) v (chartInv x z) =
    ∑ i, ∑ j, (1 / 2 : ℝ) * (realMetricFn (h t) x z)⁻¹ i j *
      fderiv ℝ (fderiv ℝ (inChart x v)) z (realVec i) (realVec j)
  calc
    _ = (1 / 2 : ℝ) * (2 * laplacian (h t) v (chartInv x z)) := by ring
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, (realMetricFn (h t) x z)⁻¹ i j *
        fderiv ℝ (fderiv ℝ (inChart x v)) z (realVec i) (realVec j)) := by rw [hh]
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end Yau.F04Proof
