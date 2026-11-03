import Yau.Proofs.P03Frames
import Yau.Proofs.P03Polynomials

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ} {M : ComplexManifold n}

theorem holomorphicFn_differentiableAt_inChart {f : M.Carrier → ℂ}
    (hf : IsHolomorphicFn f) (p : M.Carrier) :
    DifferentiableAt ℂ (inChart p f) (chartPt p p) := by
  have h := ((hf p).mdifferentiableWithinAt (s := Set.univ)).differentiableWithinAt_comp_extChartAt_symm
  have hd := h.differentiableAt (by simp [ComplexModel])
  change DifferentiableAt ℂ (fun z => f ((extChartAt (ComplexModel n) p).symm z))
    ((extChartAt (ComplexModel n) p) p)
  convert! hd using 1

/-- The first-order part of the original iterated-derivative jet equality
determines the actual complex Fréchet derivative in the same chart. -/
theorem jetAgreeFn_fderiv {f : M.Carrier → ℂ} {p : M.Carrier}
    {P : MvPolynomial (Fin n) ℂ} {k : ℕ}
    (hf : DifferentiableAt ℂ (inChart p f) (chartPt p p))
    (hjet : JetAgreeFn f p P k) (hk : 1 ≤ k) :
    fderiv ℂ (inChart p f) (chartPt p p) =
      fderiv ℂ (fun z : ComplexVector n =>
        MvPolynomial.eval (fun i => z i - chartPt p p i) P) (chartPt p p) := by
  ext v
  have h := DFunLike.congr_fun (hjet 1 hk) (fun _ : Fin 1 => v)
  have hP := centeredPolynomial_differentiable P (chartPt p p) (chartPt p p)
  have hz : fderiv ℂ (inChart p f) (chartPt p p) v -
      fderiv ℂ (fun z : ComplexVector n =>
        MvPolynomial.eval (fun i => z i - chartPt p p i) P) (chartPt p p) v = 0 := by
    simpa [iteratedFDeriv_one_apply, fderiv_fun_sub hf hP] using h
  exact sub_eq_zero.mp hz

theorem jetAgreeFn_variable_fderiv {f : M.Carrier → ℂ} {p : M.Carrier}
    {i : Fin n} {k : ℕ} (hf : IsHolomorphicFn f)
    (hjet : JetAgreeFn f p (MvPolynomial.X i) k) (hk : 1 ≤ k) :
    fderiv ℂ (inChart p f) (chartPt p p) = EuclideanSpace.proj i := by
  rw [jetAgreeFn_fderiv (holomorphicFn_differentiableAt_inChart hf p) hjet hk]
  simp only [MvPolynomial.eval_X]
  simpa only [EuclideanSpace.coe_proj] using
    ((EuclideanSpace.proj i : ComplexVector n →L[ℂ] ℂ).hasFDerivAt.sub_const
      (chartPt p p i)).fderiv

/-- Arbitrary finite scalar interpolation supplies global coordinate
functions whose native chart differentials form a basis at the chosen point. -/
theorem scalar_jets_coordinate_differentials
    (hjets : ∀ (pts : Finset M.Carrier) (k : ℕ)
      (Pj : M.Carrier → MvPolynomial (Fin n) ℂ),
      ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k)
    (p : M.Carrier) :
    ∃ f : Fin n → M.Carrier → ℂ,
      (∀ i, IsHolomorphicFn (f i)) ∧
      ∀ i, fderiv ℂ (inChart p (f i)) (chartPt p p) = EuclideanSpace.proj i := by
  classical
  have h (i : Fin n) : ∃ f : M.Carrier → ℂ,
      IsHolomorphicFn f ∧ JetAgreeFn f p (MvPolynomial.X i) 1 := by
    obtain ⟨f, hf, hj⟩ := hjets {p} 1 (fun _ => MvPolynomial.X i)
    exact ⟨f, hf, hj p (by simp)⟩
  choose f hf hj using h
  exact ⟨f, hf, fun i => jetAgreeFn_variable_fderiv (hf i) (hj i) le_rfl⟩

end Yau.NodeProofs.P03Aux
