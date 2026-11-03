import Yau.Proofs.P03SectionArrayGlue

open scoped Manifold Topology
open Set

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n} {ι : Type*}

variable (a : ι → M.Carrier) (r : ι → ℝ)
  (hsub : ∀ i, chartClosedBall (a i) (r i) ⊆ chartTarget (a i))

def fieldSectionArray (V : VectorField M) (hV : IsHolomorphicField V) : SectionArrays a r :=
  fun i => ⟨fun z => fieldCoords V (a i) z,
    continuousOn_iff_continuous_domRestrict.mp
      ((((holomorphicField_iff_chartDifferentiable V).mp hV (a i)).continuousOn).mono
        (hsub i))⟩

theorem fieldSectionArray_compatible (V : VectorField M) (hV : IsHolomorphicField V) :
    fieldSectionArray a r hsub V hV ∈ compatibleSectionArrays a r := by
  unfold compatibleSectionArrays
  apply (Submodule.mem_iInf _).mpr
  intro i
  apply (Submodule.mem_iInf _).mpr
  intro j
  apply (Submodule.mem_iInf _).mpr
  intro x
  apply (Submodule.mem_iInf _).mpr
  intro hsi
  apply (Submodule.mem_iInf _).mpr
  intro hsj
  apply (Submodule.mem_iInf _).mpr
  intro hi
  apply (Submodule.mem_iInf _).mpr
  intro hj
  apply LinearMap.mem_ker.mpr
  change chartVec (a i) x (fieldCoords V (a i) (chartPt (a i) x)) -
    chartVec (a j) x (fieldCoords V (a j) (chartPt (a j) x)) = 0
  have hci : fieldCoords V (a i) (chartPt (a i) x) = tangentCoords (a i) x (V x) := by
    change tangentCoords (a i)
      ((extChartAt (ComplexModel n) (a i)).symm ((extChartAt (ComplexModel n) (a i)) x))
      (V ((extChartAt (ComplexModel n) (a i)).symm ((extChartAt (ComplexModel n) (a i)) x))) = _
    rw [(extChartAt (ComplexModel n) (a i)).left_inv hsi]
  have hcj : fieldCoords V (a j) (chartPt (a j) x) = tangentCoords (a j) x (V x) := by
    change tangentCoords (a j)
      ((extChartAt (ComplexModel n) (a j)).symm ((extChartAt (ComplexModel n) (a j)) x))
      (V ((extChartAt (ComplexModel n) (a j)).symm ((extChartAt (ComplexModel n) (a j)) x))) = _
    rw [(extChartAt (ComplexModel n) (a j)).left_inv hsj]
  rw [hci, hcj, chartVec_tangentCoords (a i) x hsi,
    chartVec_tangentCoords (a j) x hsj, sub_self]

theorem fieldSectionArray_CR (V : VectorField M) (hV : IsHolomorphicField V) :
    fieldSectionArray a r hsub V hV ∈ CRSectionArrays a r := by
  unfold CRSectionArrays
  apply (Submodule.mem_iInf _).mpr
  intro j
  apply (Submodule.mem_iInf _).mpr
  intro α
  apply (Submodule.mem_iInf _).mpr
  intro i
  apply (Submodule.mem_iInf _).mpr
  intro ψ
  apply (Submodule.mem_iInf _).mpr
  intro hψ
  apply (Submodule.mem_iInf _).mpr
  intro hc
  apply (Submodule.mem_iInf _).mpr
  intro hs
  apply LinearMap.mem_ker.mpr
  change compactBallCRTestCLM (a j) (r j) α i ψ hψ
    (fieldSectionArray a r hsub V hV j) = 0
  rw [compactBallCRTestCLM_apply_extension]
  let b := fieldSectionArray a r hsub V hV j
  have heq : EqOn (compactBallExtension (a j) (r j) b) (fieldCoords V (a j))
      (chartClosedBall (a j) (r j)) := by
    intro z hz
    simp only [compactBallExtension, dif_pos hz]
    rfl
  have hhol : DifferentiableOn ℂ (compactBallExtension (a j) (r j) b)
      (Metric.ball (chartPt (a j) (a j)) (r j)) :=
    (((holomorphicField_iff_chartDifferentiable V).mp hV (a j)).mono
      (Metric.ball_subset_closedBall.trans (hsub j))).congr
        (heq.mono Metric.ball_subset_closedBall)
  have hscalar := (differentiableOn_piLp 2).mp hhol α
  exact (continuous_holomorphic_iff_weakCR Metric.isOpen_ball hscalar.continuousOn).mp
    hscalar i ψ hψ hc hs

/-- Every genuine global holomorphic tangent field satisfies the concrete
closed coordinate equations. -/
def fieldClosedSectionArray (V : VectorField M) (hV : IsHolomorphicField V) :
    closedSectionArrays a r :=
  ⟨fieldSectionArray a r hsub V hV,
    fieldSectionArray_compatible a r hsub V hV, fieldSectionArray_CR a r hsub V hV⟩

theorem sectionArrayField_fieldClosedSectionArray
    (hcover : ∀ x : M.Carrier, ∃ i,
      x ∈ (extChartAt (ComplexModel n) (a i)).source ∧
      chartPt (a i) x ∈ Metric.ball (chartPt (a i) (a i)) (r i))
    (V : VectorField M) (hV : IsHolomorphicField V) :
    sectionArrayField a r hcover (fieldClosedSectionArray a r hsub V hV) = V := by
  funext x
  obtain ⟨i, hsi, hi⟩ := hcover x
  rw [sectionArrayField_eq a r hcover _ i x hsi (Metric.ball_subset_closedBall hi)]
  change chartVec (a i) x (fieldCoords V (a i) (chartPt (a i) x)) = V x
  have heq : chartInv (a i) (chartPt (a i) x) = x :=
    (extChartAt (ComplexModel n) (a i)).left_inv hsi
  change chartVec (a i) x
    (tangentCoords (a i) (chartInv (a i) (chartPt (a i) x))
      (V (chartInv (a i) (chartPt (a i) x)))) = V x
  rw [heq]
  exact chartVec_tangentCoords (a i) x hsi (V x)

theorem fieldClosedSectionArray_sectionArrayField
    (hcover : ∀ x : M.Carrier, ∃ i,
      x ∈ (extChartAt (ComplexModel n) (a i)).source ∧
      chartPt (a i) x ∈ Metric.ball (chartPt (a i) (a i)) (r i))
    (b : closedSectionArrays a r) :
    fieldClosedSectionArray a r hsub (sectionArrayField a r hcover b)
      (sectionArrayField_holomorphic a r hcover b hsub) = b := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro z
  change fieldCoords (sectionArrayField a r hcover b) (a i) z = b.1 i z
  rw [fieldCoords_sectionArrayField_eq a r hcover b hsub i z.2]
  simp only [compactBallExtension, dif_pos z.2]

end Yau.NodeProofs.P03Aux
