import Yau.Proofs.D02CurvatureComposition

/-! Finite-dimensional Wirtinger calculus for the actual dual Bochner
calculation. These are ordinary product rules, including zero-dimensional
fibres. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.D02Aux
open Yau Yau.LeafProofs.L14Aux

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {r : ℕ}

def vectorWirt (t : V → Fin r → ℂ) (z v : V) : Fin r → ℂ :=
  fun a => wirt (fun w => t w a) z v

def vectorWirtBar (t : V → Fin r → ℂ) (z v : V) : Fin r → ℂ :=
  fun a => wirtBar (fun w => t w a) z v

def directionMatrixWirt (D : V → Matrix (Fin r) (Fin r) ℂ) (z v : V) :
    Matrix (Fin r) (Fin r) ℂ := fun a b => wirt (fun w => D w a b) z v

def directionMatrixWirtBar (D : V → Matrix (Fin r) (Fin r) ℂ) (z v : V) :
    Matrix (Fin r) (Fin r) ℂ := fun a b => wirtBar (fun w => D w a b) z v

theorem vectorWirt_mulVec (D : V → Matrix (Fin r) (Fin r) ℂ) (t : V → Fin r → ℂ)
    (z v : V) (hD : ∀ a b, DifferentiableAt ℝ (fun w => D w a b) z)
    (ht : ∀ a, DifferentiableAt ℝ (fun w => t w a) z) :
    vectorWirt (fun w => D w *ᵥ t w) z v =
      directionMatrixWirt D z v *ᵥ t z + D z *ᵥ vectorWirt t z v := by
  funext a
  change wirt (fun w => ∑ b, D w a b * t w b) z v = _
  rw [wirt_sum_fun Finset.univ (fun b w => D w a b * t w b) z v
    (fun b _ => (hD a b).mul (ht b))]
  simp_rw [wirt_mul_rule _ _ z v (hD a _) (ht _)]
  simp only [directionMatrixWirt, vectorWirt, Matrix.mulVec, dotProduct,
    Pi.add_apply, Finset.sum_add_distrib]

theorem vectorWirtBar_mulVec (D : V → Matrix (Fin r) (Fin r) ℂ) (t : V → Fin r → ℂ)
    (z v : V) (hD : ∀ a b, DifferentiableAt ℝ (fun w => D w a b) z)
    (ht : ∀ a, DifferentiableAt ℝ (fun w => t w a) z) :
    vectorWirtBar (fun w => D w *ᵥ t w) z v =
      directionMatrixWirtBar D z v *ᵥ t z + D z *ᵥ vectorWirtBar t z v := by
  funext a
  change wirtBar (fun w => ∑ b, D w a b * t w b) z v = _
  rw [wirtBar_sum_fun Finset.univ (fun b w => D w a b * t w b) z v
    (fun b _ => (hD a b).mul (ht b))]
  simp_rw [wirtBar_mul_rule _ _ z v (hD a _) (ht _)]
  simp only [directionMatrixWirtBar, vectorWirtBar, Matrix.mulVec, dotProduct,
    Pi.add_apply, Finset.sum_add_distrib]

theorem wirtBar_star_dotProduct (t s : V → Fin r → ℂ) (z v : V)
    (ht : ∀ a, DifferentiableAt ℝ (fun w => t w a) z)
    (hs : ∀ a, DifferentiableAt ℝ (fun w => s w a) z) :
    wirtBar (fun w => star (t w) ⬝ᵥ s w) z v =
      star (vectorWirt t z v) ⬝ᵥ s z + star (t z) ⬝ᵥ vectorWirtBar s z v := by
  change wirtBar (fun w => ∑ a, star (t w a) * s w a) z v = _
  rw [wirtBar_sum_fun Finset.univ (fun a w => star (t w a) * s w a) z v
    (fun a _ => (ht a).star.mul (hs a))]
  simp_rw [wirtBar_mul_rule _ _ z v (ht _).star (hs _), wirtBar_star]
  simp only [vectorWirt, vectorWirtBar, dotProduct, Pi.star_apply, Finset.sum_add_distrib]

theorem wirt_holomorphic_pairing (η t : V → Fin r → ℂ) (z v : V)
    (hη : ∀ a, DifferentiableAt ℂ (fun w => η w a) z)
    (ht : ∀ a, DifferentiableAt ℝ (fun w => t w a) z) :
    wirt (fun w => star (η w) ⬝ᵥ t w) z v = star (η z) ⬝ᵥ vectorWirt t z v := by
  have h0 (a : Fin r) : wirt (fun w => star (η w a)) z v = 0 := by
    rw [wirt_star, wirtBar_eq_zero_of_complex_differentiable _ z v (hη a), star_zero]
  change wirt (fun w => ∑ a, star (η w a) * t w a) z v = _
  rw [wirt_sum_fun Finset.univ (fun a w => star (η w a) * t w a) z v
    (fun a _ => ((hη a).restrictScalars ℝ).star.mul (ht a))]
  simp_rw [wirt_mul_rule _ _ z v ((hη _).restrictScalars ℝ).star (ht _), h0,
    zero_mul, zero_add]
  rfl

theorem vectorWirt_lowering {U : Set V} (hU : IsOpen U)
    (D : V → Matrix (Fin r) (Fin r) ℂ) (t η : V → Fin r → ℂ)
    (hLower : ∀ w ∈ U, D w *ᵥ t w = η w) (z v : V) (hz : z ∈ U)
    (hD : ∀ a b, DifferentiableAt ℝ (fun w => D w a b) z)
    (ht : ∀ a, DifferentiableAt ℝ (fun w => t w a) z) :
    directionMatrixWirt D z v *ᵥ t z + D z *ᵥ vectorWirt t z v = vectorWirt η z v := by
  rw [← vectorWirt_mulVec D t z v hD ht]
  funext a
  have he : (fun w => (D w *ᵥ t w) a) =ᶠ[𝓝 z] (fun w => η w a) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrFun (hLower w hw) a
  unfold vectorWirt wirt
  rw [he.fderiv_eq]

theorem vectorWirtBar_lowering {U : Set V} (hU : IsOpen U)
    (D : V → Matrix (Fin r) (Fin r) ℂ) (t η : V → Fin r → ℂ)
    (hLower : ∀ w ∈ U, D w *ᵥ t w = η w) (z v : V) (hz : z ∈ U)
    (hD : ∀ a b, DifferentiableAt ℝ (fun w => D w a b) z)
    (ht : ∀ a, DifferentiableAt ℝ (fun w => t w a) z) :
    directionMatrixWirtBar D z v *ᵥ t z + D z *ᵥ vectorWirtBar t z v = vectorWirtBar η z v := by
  rw [← vectorWirtBar_mulVec D t z v hD ht]
  funext a
  have he : (fun w => (D w *ᵥ t w) a) =ᶠ[𝓝 z] (fun w => η w a) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrFun (hLower w hw) a
  unfold vectorWirtBar wirtBar
  rw [he.fderiv_eq]

end Yau.NodeProofs.D02Aux
