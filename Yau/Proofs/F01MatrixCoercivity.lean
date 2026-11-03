import Yau.Proofs.F01CompactCoercivity

/-! Compact positive Hermitian matrix families give actual uniform quadratic
bounds in the Euclidean norm, including the empty index type. -/
open Set Matrix
open scoped ComplexOrder
noncomputable section
namespace Yau.NodeProofs.F01Aux
variable {ι : Type*} [Fintype ι]

def matrixRealBilinearLinear (G : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => (star (WithLp.ofLp u) ⬝ᵥ (G *ᵥ WithLp.ofLp v)).re)
    (by intro u v w; simp only [WithLp.ofLp_add, star_add, add_dotProduct, Complex.add_re])
    (by intro r u v; simp only [WithLp.ofLp_smul, star_smul, star_trivial,
      smul_dotProduct, Complex.smul_re, smul_eq_mul])
    (by intro u v w; simp only [WithLp.ofLp_add, Matrix.mulVec_add, dotProduct_add, Complex.add_re])
    (by intro r u v; simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, dotProduct_smul,
      Complex.smul_re, smul_eq_mul])

def matrixRealBilinear (G : Matrix ι ι ℂ) :
    EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ :=
  let T : (EuclideanSpace ℂ ι →ₗ[ℝ] ℝ) →ₗ[ℝ] (EuclideanSpace ℂ ι →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℂ ι →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (EuclideanSpace ℂ ι →L[ℝ] ℝ)).toLinearMap
  LinearMap.toContinuousLinearMap (T.comp (matrixRealBilinearLinear G))

theorem matrixRealBilinear_apply (G : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) :
    matrixRealBilinear G u v = (star (WithLp.ofLp u) ⬝ᵥ (G *ᵥ WithLp.ofLp v)).re := rfl

def matrixRealBilinearMap : (ι → ι → ℂ) →ₗ[ℝ]
    EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ where
  toFun := matrixRealBilinear
  map_add' G H := by
    ext u v
    change (star (WithLp.ofLp u) ⬝ᵥ ((Matrix.of G + Matrix.of H) *ᵥ WithLp.ofLp v)).re =
      (star (WithLp.ofLp u) ⬝ᵥ (Matrix.of G *ᵥ WithLp.ofLp v)).re +
      (star (WithLp.ofLp u) ⬝ᵥ (Matrix.of H *ᵥ WithLp.ofLp v)).re
    simp only [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  map_smul' r G := by
    ext u v
    change (star (WithLp.ofLp u) ⬝ᵥ ((r • Matrix.of G) *ᵥ WithLp.ofLp v)).re =
      r * (star (WithLp.ofLp u) ⬝ᵥ (Matrix.of G *ᵥ WithLp.ofLp v)).re
    simp only [Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul]

theorem compact_posDef_quadratic_bounds {A : Type*} [TopologicalSpace A]
    {K : Set A} (hK : IsCompact K) {G : A → Matrix ι ι ℂ}
    (hG : ContinuousOn G K) (hpos : ∀ a ∈ K, (G a).PosDef) :
    ∃ ℓ C : ℝ, 0 < ℓ ∧ 0 < C ∧ ∀ a ∈ K, ∀ v : EuclideanSpace ℂ ι,
      ℓ * ‖v‖ ^ 2 ≤ (star (WithLp.ofLp v) ⬝ᵥ (G a *ᵥ WithLp.ofLp v)).re ∧
      (star (WithLp.ofLp v) ⬝ᵥ (G a *ᵥ WithLp.ofLp v)).re ≤ C * ‖v‖ ^ 2 := by
  let T : (ι → ι → ℂ) →L[ℝ]
      EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := ι → ι → ℂ)
      (F' := EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι →L[ℝ] ℝ)
      (matrixRealBilinearMap (ι := ι))
  have hB : ContinuousOn (fun a => matrixRealBilinear (G a)) K :=
    T.continuous.comp_continuousOn hG
  apply compact_positive_bilinear_bounds hK hB
  intro a ha v hv
  have hnv : WithLp.ofLp v ≠ 0 := by
    intro hzero
    apply hv
    exact (WithLp.ofLp_injective (p := 2)) (by simpa only [WithLp.ofLp_zero] using hzero)
  exact (Complex.pos_iff.mp ((hpos a ha).dotProduct_mulVec_pos hnv)).1

end Yau.NodeProofs.F01Aux
