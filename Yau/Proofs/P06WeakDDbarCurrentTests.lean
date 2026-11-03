import Yau.Proofs.P06WeakDDbarCurrentChart

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.P06Aux.WeakCurrent
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Yau.NodeProofs.G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

/-- The supported positive matrix test includes the genuine volume density
and both inverse Hermitian metric factors. -/
def chartMatrixTest (g : HermitianField M) (B : RealForm M 2)
    (c : M.Carrier) (z : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  by
    classical
    exact if z ∈ chartTarget c then weightedChartMatrix g B c z else 0

theorem chartHermitianMatrix_zero_at (B : RealForm M 2) (c : M.Carrier)
    (z : ComplexVector n) (hz : B (chartInv c z) = 0) :
    chartHermitianMatrix B c z = 0 := by
  ext a b
  simp [chartHermitianMatrix, alternatingMatrix, chartForm, hz]

theorem chartMatrixTest_nonnegative (g : HermitianField M) (B : RealForm M 2)
    (h11 : RealOneOne B) (hp : FormLE 0 B) (c : M.Carrier) (z : ComplexVector n) :
    (chartMatrixTest g B c z).PosSemidef := by
  by_cases hz : z ∈ chartTarget c
  · simpa only [chartMatrixTest, if_pos hz] using weightedChartMatrix_nonnegative g B h11 hp c hz
  · simp only [chartMatrixTest, if_neg hz]
    exact Matrix.PosSemidef.zero

theorem weightedChartMatrix_contDiffOn (g : SmoothMetric M) (B : RealForm M 2)
    (hB : SmoothRealForm B) (c : M.Carrier) (a b : Fin n) :
    ContDiffOn ℝ ∞ (fun z => weightedChartMatrix g.form B c z a b) (chartTarget c) := by
  have hρ := Complex.ofRealCLM.contDiff.comp_contDiffOn (L18Aux.volumeDensity_contDiffOn g c)
  have hi := L18Aux.hMat_inverse_contDiffOn g c
  simp only [weightedChartMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  apply hρ.mul
  apply ContDiffOn.sum
  intro j _
  apply ContDiffOn.mul _ (hi j b)
  apply ContDiffOn.sum
  intro i _
  exact (hi a i).mul (chartHermitianMatrix_contDiffOn B hB c i j)

/-- All regularity and support premises of the parent's local matrix-test
inequality are constructed from the actual compact chart-supported form. -/
theorem chartMatrixTest_regular (g : SmoothMetric M) (B : RealForm M 2)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) (c : M.Carrier)
    (hBc : closure {y | B y ≠ 0} ⊆ (extChartAt (ComplexModel n) c).source) :
    ∀ a b, ContDiff ℝ ∞ (fun z => chartMatrixTest g.form B c z a b) ∧
      HasCompactSupport (fun z => chartMatrixTest g.form B c z a b) ∧
      tsupport (fun z => chartMatrixTest g.form B c z a b) ⊆ chartTarget c := by
  let K := chartPt c '' closure {y | B y ≠ 0}
  have hK : IsCompact K := hcB.image_of_continuousOn
    ((continuousOn_extChartAt (I := ComplexModel n) c).mono hBc)
  have hKO : K ⊆ chartTarget c := by
    rintro z ⟨y, hy, rfl⟩
    exact (extChartAt (ComplexModel n) c).map_source (hBc hy)
  have hs (a b : Fin n) : tsupport (fun z => chartMatrixTest g.form B c z a b) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hzK
    apply hz
    by_cases hzo : z ∈ chartTarget c
    · have hzB : B (chartInv c z) = 0 := by
        by_contra hn
        exact hzK ⟨chartInv c z, subset_closure hn,
          (extChartAt (ComplexModel n) c).right_inv hzo⟩
      simp only [chartMatrixTest, if_pos hzo, weightedChartMatrix,
        chartHermitianMatrix_zero_at B c z hzB, Matrix.mul_zero, Matrix.zero_mul, smul_zero,
        Matrix.zero_apply]
    · simp only [chartMatrixTest, if_neg hzo, Matrix.zero_apply]
  intro a b
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) (hs a b), (hs a b).trans hKO⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ K
  · have hzo := hKO hz
    have heq : (fun w => chartMatrixTest g.form B c w a b) =ᶠ[𝓝 z]
        (fun w => weightedChartMatrix g.form B c w a b) := by
      filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hzo] with w hw
      have hwO : w ∈ chartTarget c := hw
      simp only [chartMatrixTest, if_pos hwO]
    exact ((weightedChartMatrix_contDiffOn g B hB c a b).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hzo)).congr_of_eventuallyEq heq
  · have heq : (fun w => chartMatrixTest g.form B c w a b) =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hK.isClosed.compl_mem_nhds hz] with w hw
      exact image_eq_zero_of_notMem_tsupport (f := fun z => chartMatrixTest g.form B c z a b)
        (fun h => hw (hs a b h))
    exact contDiffAt_const.congr_of_eventuallyEq heq

end Yau.NodeProofs.P06Aux.WeakCurrent
