import Yau.Proofs.P06WeitzenbockSpectralEnergy
import Yau.Proofs.P06WeitzenbockQuadratic

noncomputable section
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.P06Weitzenbock
open Yau G01Aux G04Aux Yau.LeafProofs
variable {n : ℕ}

theorem relativeReactionEnergy_eq_contraction
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hR : ∀ i j k l, R i j k l = R k l i j)
    (H A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (H * (finiteCurvatureAction R H * H * A +
        A * H * finiteCurvatureAction R H - (2 : ℂ) • finiteCurvatureAction R (H * A * H)) * H * A) =
      2 * curvatureContraction R H (H * A * H * A * H) -
        2 * curvatureContraction R (H * A * H) (H * A * H) := by
  let Rc := finiteCurvatureAction R H
  let B := H * A * H
  let C := finiteCurvatureAction R B
  let S := H * A * H * A * H
  have h₁ : Matrix.trace (H * (Rc * H * A) * H * A) = Matrix.trace (S * Rc) := by
    calc
      _ = Matrix.trace (H * (Rc * H * A * H * A)) := by congr 1; noncomm_ring
      _ = Matrix.trace ((Rc * H * A * H * A) * H) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Rc * S) := by congr 1; dsimp [S]; noncomm_ring
      _ = _ := Matrix.trace_mul_comm _ _
  have h₂ : Matrix.trace (H * (A * H * Rc) * H * A) = Matrix.trace (S * Rc) := by
    calc
      _ = Matrix.trace ((H * A * H) * (Rc * H * A)) := by congr 1; noncomm_ring
      _ = Matrix.trace ((Rc * H * A) * (H * A * H)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (Rc * S) := by congr 1; dsimp [S]; noncomm_ring
      _ = _ := Matrix.trace_mul_comm _ _
  have h₃ : Matrix.trace (H * C * H * A) = Matrix.trace (B * C) := by
    calc
      _ = Matrix.trace ((H * C) * (H * A)) := by congr 1; noncomm_ring
      _ = Matrix.trace ((H * A) * (H * C)) := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; dsimp [B]; noncomm_ring
  change Matrix.trace (H * (Rc * H * A + A * H * Rc - (2 : ℂ) • C) * H * A) = _
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul]
  rw [h₁, h₂, h₃]
  change Matrix.trace (S * finiteCurvatureAction R H) +
      Matrix.trace (S * finiteCurvatureAction R H) -
      2 * Matrix.trace (B * finiteCurvatureAction R B) = _
  rw [← curvatureContraction_eq_trace, ← curvatureContraction_eq_trace,
    curvatureContraction_comm R hR S H]
  dsimp only [S, B]
  ring

theorem relativeReactionEnergy_spectral
    (R : Fin n → Fin n → Fin n → Fin n → ℂ)
    (hR : ∀ i j k l, R i j k l = R k l i j)
    (H E : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (hE : Eᴴ * H * E = 1)
    (eig : Fin n → ℝ) :
    let A := H * E * Matrix.diagonal (fun i => (eig i : ℂ)) * Eᴴ * H
    (Matrix.trace (H⁻¹ * (finiteCurvatureAction R H⁻¹ * H⁻¹ * A +
        A * H⁻¹ * finiteCurvatureAction R H⁻¹ -
          (2 : ℂ) • finiteCurvatureAction R (H⁻¹ * A * H⁻¹)) * H⁻¹ * A)).re =
      diagonalCurvatureEnergy (fun i j => (frameCurvatureCoefficient R E i j).re) eig := by
  dsimp only
  rw [relativeReactionEnergy_eq_contraction R hR,
    raised_spectral_square H E hH hE]
  simp only [raised_spectral_form H E hH]
  rw [inverseMetric_eq_unitary_frame H E hH hE]
  have hD : Matrix.diagonal (fun i => (eig i : ℂ)) *
      Matrix.diagonal (fun i => (eig i : ℂ)) =
      Matrix.diagonal (fun i => (((eig i) ^ 2 : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.mul_apply, Complex.ofReal_pow, pow_two, Complex.ofReal_mul]
  rw [hD]
  exact curvatureContraction_spectral_energy R hR E eig

end Yau.NodeProofs.P06Weitzenbock
