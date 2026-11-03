import Yau.Proofs.F01AffineChangedChart
import Yau.Proofs.F01SimultaneousHermitian
import Yau.Proofs.F01KahlerAffineJet
import Yau.Proofs.F01KahlerJetSymmetry
import Yau.Proofs.F01OrdinaryMetricData

/-! Actual affine metric matrices, their Kähler first-jet symmetry, and
simultaneous normalization using the original fixed-chart coefficients. -/
noncomputable section
open Set
open scoped Matrix ContDiff ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

def affineMetricMatrix (g : HermitianField M) (p : M.Carrier)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) (z : ComplexVector n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Aᴴ * hMat g p (affineCoordinateHomeomorph (chartPt p p) A hA z) * A

theorem affineMetricMatrix_zero (g : HermitianField M) (p : M.Carrier)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    affineMetricMatrix g p A hA 0 = Aᴴ * gMat g p * A := by
  unfold affineMetricMatrix
  rw [affineCoordinateHomeomorph_apply, map_zero, add_zero]
  rfl

theorem affineMetricMatrix_entry_differentiableAt (g : HermitianField M)
    (hg : MetricSmooth g) (p : M.Carrier) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A)
    {z : ComplexVector n} (hz : affineCoordinateHomeomorph (chartPt p p) A hA z ∈ chartTarget p)
    (i j : Fin n) : DifferentiableAt ℝ (fun w => affineMetricMatrix g p A hA w i j) z := by
  have hT := ((affineCoordinateHomeomorph_contDiff (chartPt p p) A hA).differentiable
    (by simp) z).restrictScalars ℝ
  have he (a b : Fin n) : DifferentiableAt ℝ
      (fun w => hMat g p (affineCoordinateHomeomorph (chartPt p p) A hA w) a b) z :=
    (((L17Aux.hMat_contDiffOn_of_metricSmooth g hg p a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) p).mem_nhds hz)).differentiableAt
        (by simp)).comp z hT
  have hterm (q a : Fin n) : DifferentiableAt ℝ
      (fun w => star (A a i) * hMat g p
        (affineCoordinateHomeomorph (chartPt p p) A hA w) a q * A q j) z :=
    ((he a q).const_mul _).mul_const _
  have hr (q : Fin n) : DifferentiableAt ℝ
      (fun w => ∑ a, star (A a i) * hMat g p
        (affineCoordinateHomeomorph (chartPt p p) A hA w) a q * A q j) z :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun a _ => hterm q a)
  have hs := DifferentiableAt.fun_sum (u := Finset.univ) (fun q _ => hr q)
  simpa only [affineMetricMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul] using hs

theorem affineMetricMatrix_wirt_symm (g : SmoothMetric M) (p : M.Carrier)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) {z : ComplexVector n}
    (hz : affineCoordinateHomeomorph (chartPt p p) A hA z ∈ chartTarget p) (i j k : Fin n) :
    wirt (fun w => affineMetricMatrix g.form p A hA w i j) z (stdVec k) =
      wirt (fun w => affineMetricMatrix g.form p A hA w i k) z (stdVec j) := by
  apply affine_congruence_wirt_symmetry
  · intro a b
    exact ((L17Aux.hMat_contDiffOn_of_metricSmooth g.form
      (L12Aux.metricSmooth_of_smoothMetric g) p a b).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) p).mem_nhds hz)).differentiableAt (by simp)
  · intro a b c
    exact smoothMetric_hMat_wirt_symm g p _ hz c b a

theorem affineMetricMatrix_eq_pullback (g : HermitianField M) (p : M.Carrier)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) {z : ComplexVector n}
    (hz : z ∈ (affineChangedChart (ordinaryChart p) (chartPt p p) A hA).source) :
    L17Aux.pullbackMatrix g (affineChangedChart (ordinaryChart p) (chartPt p p) A hA) z =
      affineMetricMatrix g p A hA z := by
  have h := affineChangedChart_pullbackMatrix g (ordinaryChart p)
    (ordinaryChart_contMDiffOn p) (chartPt p p) A hA hz
  have hz' : affineCoordinateHomeomorph (chartPt p p) A hA z ∈ chartTarget p := by
    have hh : affineCoordinateHomeomorph (chartPt p p) A hA z ∈ (ordinaryChart p).source := hz.2
    simpa only [ordinaryChart_source] using hh
  have he : L17Aux.pullbackMatrix g (ordinaryChart p)
      (affineCoordinateHomeomorph (chartPt p p) A hA z) =
      hMat g p (affineCoordinateHomeomorph (chartPt p p) A hA z) := by
    ext i j
    exact ordinaryChart_Gram g p hz' i j
  change L17Aux.pullbackMatrix g (affineChangedChart (ordinaryChart p) (chartPt p p) A hA) z =
    Aᴴ * L17Aux.pullbackMatrix g (ordinaryChart p)
      (affineCoordinateHomeomorph (chartPt p p) A hA z) * A at h
  rw [he] at h
  exact h

theorem exists_normalizing_affine_metric (g k : HermitianField M) (p : M.Carrier) :
    ∃ (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A),
      affineMetricMatrix g p A hA 0 = 1 ∧ ∃ values : Fin n → ℝ,
        affineMetricMatrix k p A hA 0 = Matrix.diagonal (fun i => (values i : ℂ)) := by
  have hH : (gMat g p).PosDef := L12Aux.hMat_posDef g p _ (mem_extChartAt_target p)
  have hK : (gMat k p).IsHermitian := L12Aux.hMat_isHermitian k p _
  obtain ⟨A, hA, hAH, values, hAK⟩ := simultaneous_hermitian_normalization (gMat g p) (gMat k p) hH hK
  exact ⟨A, hA, by rw [affineMetricMatrix_zero]; exact hAH,
    values, by rw [affineMetricMatrix_zero]; exact hAK⟩

end Yau.NodeProofs.F01Aux
