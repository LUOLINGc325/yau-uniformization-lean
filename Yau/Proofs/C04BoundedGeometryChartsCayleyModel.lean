import Yau.Proofs.C04BoundedGeometryChartsNormalComplexStructure
import Yau.LeafProofs.L21GraphIntertwining

/-! The Cayley graph is one fixed smooth function of the real coframe near the identity. -/
noncomputable section
open Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace Yau.Proofs.C04ChartsAux
open Yau Yau.LeafProofs.L21Aux
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5

def coframeComplexModel (n : ℕ) (A : ComplexVector n →L[ℝ] ComplexVector n) :
    ComplexVector n →L[ℝ] ComplexVector n :=
  A.inverse.comp ((stdComplex n).comp A)

def coframeCayleyGraphModel (n : ℕ) (A : ComplexVector n →L[ℝ] ComplexVector n) :
    Matrix (Fin n) (Fin n) ℂ := fun i k => cayleyMap (coframeComplexModel n A) (stdVec i) k

@[simp] theorem coframeComplexModel_id (n : ℕ) :
    coframeComplexModel n (ContinuousLinearMap.id ℝ (ComplexVector n)) = stdComplex n := by
  simp only [coframeComplexModel, ContinuousLinearMap.inverse_id, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.id_comp]

@[simp] theorem coframeCayleyGraphModel_id (n : ℕ) :
    coframeCayleyGraphModel n (ContinuousLinearMap.id ℝ (ComplexVector n)) = 0 := by
  apply Matrix.ext
  intro i k
  change cayleyMap (coframeComplexModel n (ContinuousLinearMap.id ℝ (ComplexVector n))) (stdVec i) k = 0
  rw [coframeComplexModel_id]
  simp only [cayleyMap, sub_self, ContinuousLinearMap.comp_zero, zero_apply]
  rfl

theorem coframeComplexModel_smoothAt (A : ComplexVector n →L[ℝ] ComplexVector n)
    (hi : A.IsInvertible) : ContDiffAt ℝ ∞ (coframeComplexModel n) A :=
  hi.contDiffAt_map_inverse.clm_comp (contDiffAt_const.clm_comp contDiffAt_id)

theorem coframeCayleyGraphModel_smoothAt (A : ComplexVector n →L[ℝ] ComplexVector n)
    (hi : A.IsInvertible) (hC : (coframeComplexModel n A + stdComplex n).IsInvertible) :
    ContDiffAt ℝ ∞ (coframeCayleyGraphModel n) A := by
  have hJ := coframeComplexModel_smoothAt A hi
  have hsum : ContDiffAt ℝ ∞ (fun L => coframeComplexModel n L + stdComplex n) A := hJ.add contDiffAt_const
  have hcinv : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse : (ComplexVector n →L[ℝ] ComplexVector n) → ComplexVector n →L[ℝ] ComplexVector n)
      (coframeComplexModel n A + stdComplex n) := hC.contDiffAt_map_inverse
  have hinv : ContDiffAt ℝ ∞ (fun L => (coframeComplexModel n L + stdComplex n).inverse) A :=
    by
      simpa only [Function.comp_def] using (hcinv.comp A hsum)
  have hCa : ContDiffAt ℝ ∞ (fun L => cayleyMap (coframeComplexModel n L)) A :=
    hinv.clm_comp (contDiffAt_const.sub hJ)
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro k
  exact ((EuclideanSpace.proj k).restrictScalars ℝ).contDiff.comp_contDiffAt A
    (hCa.clm_apply contDiffAt_const)

theorem exists_coframe_cayley_model_neighborhood (n : ℕ) :
    ∃ d : ℝ, 0 < d ∧ ∀ A : ComplexVector n →L[ℝ] ComplexVector n,
      ‖A - ContinuousLinearMap.id ℝ (ComplexVector n)‖ < d →
      A.IsInvertible ∧ (coframeComplexModel n A + stdComplex n).IsInvertible := by
  let Id := ContinuousLinearMap.id ℝ (ComplexVector n)
  have hi : Id.IsInvertible := ⟨ContinuousLinearEquiv.refl ℝ (ComplexVector n), rfl⟩
  have hJ := coframeComplexModel_smoothAt Id hi
  have hC : (coframeComplexModel n Id + stdComplex n).IsInvertible := by
    rw [coframeComplexModel_id]
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := (- (1 / 2 : ℝ)) • stdComplex n)
    · apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, stdComplex_apply,
        smul_add, smul_smul, Complex.I_mul_I, ContinuousLinearMap.id_apply]
      module_nf <;> simp [Complex.I_sq]
    · apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply, stdComplex_apply,
        smul_add, smul_smul, Complex.I_mul_I, ContinuousLinearMap.id_apply]
      module_nf <;> simp [Complex.I_sq]
  have hh : ∀ᶠ A in 𝓝 Id,
      A.IsInvertible ∧ (coframeComplexModel n A + stdComplex n).IsInvertible :=
    hi.eventually_nhds.and ((hJ.add contDiffAt_const).continuousAt.eventually hC.eventually_nhds)
  obtain ⟨d, hd, hb⟩ := Metric.mem_nhds_iff.mp hh
  refine ⟨d, hd, ?_⟩
  intro A hA
  exact hb (by simpa only [Metric.mem_ball, dist_eq_norm] using hA)

end Yau.Proofs.C04ChartsAux
