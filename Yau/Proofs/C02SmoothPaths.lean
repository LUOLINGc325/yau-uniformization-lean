import Yau.LeafProofs.L23FieldMetric

/-! Smooth near-minimizers for the project's actual length infimum.
The same smooth path is admissible for every other smooth Hermitian field. -/

noncomputable section
open scoped Manifold ENNReal
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_smooth_nearMinimizingCurve (k : HermitianField M) (hk : MetricSmooth k)
    (x y : M.Carrier) (ε : ℝ) (hε : 0 < ε) :
    letI := L12Aux.manifold_realSmooth M
    ∃ γ : IntegrableCurve k x y,
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ.1.toFun ∧
      curveLength k γ.1 < inducedDistance k x y + ε := by
  let := L12Aux.manifold_realSmooth M
  let : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentNormedAddCommGroup k z
  let : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentInnerProductSpace k z
  have hpos : 0 < inducedDistance k x y + ε :=
    add_pos_of_nonneg_of_pos (L23Aux.inducedDistance_nonneg k hk x y) hε
  have hr : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y <
      ENNReal.ofReal (inducedDistance k x y + ε) := by
    rw [← L23Aux.inducedDistance_eq_riemannianEDist k hk x y]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (lt_add_of_pos_right _ hε)
  obtain ⟨f, hx, hy, hf, hlen, _, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  subst x
  subst y
  let γ := L23Aux.integrableCurve_of_contMDiff k hk hf
  have hPath := L12Aux.curveLength_eq_pathELength k γ
  change ENNReal.ofReal (curveLength k γ.1) =
    Manifold.pathELength 𝓘(ℝ, ComplexVector n) f 0 1 at hPath
  rw [← hPath] at hlen
  exact ⟨γ, hf, (ENNReal.ofReal_lt_ofReal_iff hpos).mp hlen⟩

end Yau.Blueprint.C02Proof
