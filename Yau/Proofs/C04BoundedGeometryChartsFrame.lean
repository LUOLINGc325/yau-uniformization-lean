import Yau.Proofs.C04BoundedGeometryChartsMetric

/-! A genuine complex unitary frame and its canonical real frame. -/

noncomputable section
open scoped Topology Manifold ContDiff Matrix InnerProductSpace

namespace Yau.Proofs.C04ChartsAux
open Module Yau Yau.LeafProofs Yau.LeafProofs.L12Aux

section HermitianBasis
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

@[instance_reducible]
def hermitianInnerProductCore (h : HermitianInnerProduct V) : InnerProductSpace.Core ℂ V where
  inner := h.toFun
  conj_inner_symm u v := (h.conjugate_symmetric u v).symm
  re_inner_nonneg u := (h.positive_definite u).1
  add_left := h.map_add_left
  smul_left u v c := h.map_smul_left c u v
  definite u hu := (h.positive_definite u).2.mp (by rw [hu]; rfl)

theorem exists_hermitian_unitary_basis {r : ℕ} (h : HermitianInnerProduct V)
    (b : Basis (Fin r) ℂ V) :
    ∃ c : Basis (Fin r) ℂ V, ∀ i j, h.toFun (c i) (c j) =
      (1 : Matrix (Fin r) (Fin r) ℂ) i j := by
  letI : InnerProductSpace.Core ℂ V := hermitianInnerProductCore h
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V :=
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  letI : FiniteDimensional ℂ V := b.finiteDimensional_of_finite
  have hdim : Module.finrank ℂ V = r := by simpa using Module.finrank_eq_card_basis b
  let c : OrthonormalBasis (Fin r) ℂ V :=
    (stdOrthonormalBasis ℂ V).reindex (finCongr hdim)
  refine ⟨c.toBasis, ?_⟩
  intro i j
  change ⟪c i, c j⟫_ℂ = (1 : Matrix (Fin r) (Fin r) ℂ) i j
  simp [c.inner_eq_ite, Matrix.one_apply]

end HermitianBasis

variable {n : ℕ} {M : ComplexManifold n}

theorem exists_complex_unitary_frame (k : HermitianField M) (p : M.Carrier) :
    ∃ U : ComplexVector n ≃L[ℂ] TangentVector M p,
      ∀ i j, (k p).toFun (U (stdVec i)) (U (stdVec j)) =
        (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  let b := (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
  let bp := b.map (tangentSpaceCastModel (ComplexModel n) p).symm.toLinearEquiv
  obtain ⟨c, hc⟩ := exists_hermitian_unitary_basis (k p) bp
  let U : ComplexVector n ≃L[ℂ] TangentVector M p :=
    (b.equiv c (Equiv.refl _)).toContinuousLinearEquiv
  have hU (i : Fin n) : U (stdVec i) = c i := by
    have hi : stdVec i = b i := by simp [b, stdVec, EuclideanSpace.basisFun_apply]
    change b.equiv c (Equiv.refl _) (stdVec i) = c i
    rw [hi]
    simp only [Basis.equiv_apply, Equiv.refl_apply]
  exact ⟨U, fun i j => by rw [hU, hU]; exact hc i j⟩

def realUnitaryFrame (p : M.Carrier) (U : ComplexVector n ≃L[ℂ] TangentVector M p) :
    ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) p :=
  (U.restrictScalars ℝ).trans (realTangentEquiv p).symm

@[simp] theorem realTangentEquiv_realUnitaryFrame (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v : ComplexVector n) :
    realTangentEquiv p (realUnitaryFrame p U v) = U v := by
  exact (realTangentEquiv p).apply_symm_apply _

theorem realUnitaryFrame_pairing (k : HermitianField M) (p : M.Carrier)
    (U : ComplexVector n ≃L[ℂ] TangentVector M p) (v w : ComplexVector n) :
    (underlyingRealRiemannianMetric k).inner p (realUnitaryFrame p U v) (realUnitaryFrame p U w) =
      2 * ((k p).toFun (U v) (U w)).re := by
  rw [underlyingRealRiemannianMetric_inner, realTangentEquiv_realUnitaryFrame,
    realTangentEquiv_realUnitaryFrame]

end Yau.Proofs.C04ChartsAux
