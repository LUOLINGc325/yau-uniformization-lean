import Yau.Proofs.P03TopPoleJets

open scoped Manifold Topology ContDiff
open Set Filter MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}
variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (Bundle.TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

theorem top_polynomial_jets_of_correction_zero (w v : NQForm E 0)
    (hw : HolomorphicTopForm (r := r) E w) (p : M.Carrier)
    (P : Fin r → MvPolynomial (Fin n) ℂ) (order : ℕ)
    (hgerm : (fun z => coefficients (r := r) E v p z Fin.elim0) =ᶠ[𝓝 (chartPt p p)]
      (fun z => WithLp.toLp 2 (fun α => MvPolynomial.eval (fun i => z i - chartPt p p i) (P α)) -
        coefficients (r := r) E w p z Fin.elim0))
    (hz : ∀ α : Fin r, ∀ j ≤ order,
      iteratedFDeriv ℂ j (fun z => coefficients (r := r) E v p z Fin.elim0 α) (chartPt p p) = 0) :
    ∀ j ≤ order, iteratedFDeriv ℂ j
      (fun z => coefficients (r := r) E w p z Fin.elim0 -
        WithLp.toLp 2 (fun α => MvPolynomial.eval (fun i => z i - chartPt p p i) (P α)))
      (chartPt p p) = 0 := by
  let F : ComplexVector n → ComplexVector r := fun z => coefficients (r := r) E w p z Fin.elim0 -
    WithLp.toLp 2 (fun α => MvPolynomial.eval (fun i => z i - chartPt p p i) (P α))
  have hP : Differentiable ℂ (fun z : ComplexVector n => WithLp.toLp 2
      (fun α => MvPolynomial.eval (fun i => z i - chartPt p p i) (P α))) :=
    (differentiable_piLp (𝕜 := ℂ) 2).mpr fun α => centeredPolynomial_differentiable (P α) (chartPt p p)
  have hF : DifferentiableOn ℂ F (localDomain (r := r) E p) :=
    ((differentiableOn_piLp (𝕜 := ℂ) 2).mpr (hw p)).sub hP.differentiableOn
  have hself : chartPt p p ∈ localDomain (r := r) E p :=
    chartPt_mem_localDomain E p p
      ⟨mem_extChartAt_source p, FiberBundle.mem_baseSet_trivializationAt' p⟩
  have hreg := (Yau.LeafProofs.L17Holomorphic.contDiffOn_of_complexDiff (localDomain_isOpen E p)
    hF (chartPt p p) hself).contDiffAt ((localDomain_isOpen E p).mem_nhds hself)
  intro j hj
  change iteratedFDeriv ℂ j F (chartPt p p) = 0
  apply ContinuousMultilinearMap.ext
  intro args
  ext α : 1
  have heq : (fun z => F z α) =ᶠ[𝓝 (chartPt p p)]
      (fun z => -coefficients (r := r) E v p z Fin.elim0 α) := by
    filter_upwards [hgerm] with z hzg
    have he := congrArg (fun z : ComplexVector r => z α) hzg
    change coefficients (r := r) E v p z Fin.elim0 α =
      MvPolynomial.eval (fun i => z i - chartPt p p i) (P α) - coefficients (r := r) E w p z Fin.elim0 α at he
    change coefficients (r := r) E w p z Fin.elim0 α -
      MvPolynomial.eval (fun i => z i - chartPt p p i) (P α) = -coefficients (r := r) E v p z Fin.elim0 α
    rw [he]
    ring
  have hsc : iteratedFDeriv ℂ j (fun z => F z α) (chartPt p p) = 0 := by
    rw [(heq.iteratedFDeriv ℂ j).self_of_nhds]
    change iteratedFDeriv ℂ j (-(fun z => coefficients (r := r) E v p z Fin.elim0 α)) (chartPt p p) = 0
    rw [iteratedFDeriv_neg_apply, hz α j hj, neg_zero]
  have hproj := (EuclideanSpace.proj α : ComplexVector r →L[ℂ] ℂ).iteratedFDeriv_comp_left
    (x := chartPt p p) hreg (show (j : ℕ∞ω) ≤ ∞ by simp)
  have he := congrArg (fun T : ComplexVector n [×j]→L[ℂ] ℂ => T args) (hproj.symm.trans hsc)
  change (iteratedFDeriv ℂ j F (chartPt p p) args) α = 0 at he
  exact he

end Yau.NodeProofs.P03Aux
