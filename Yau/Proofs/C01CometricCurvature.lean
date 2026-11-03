import Yau.Proofs.C01MixedInverseJets
import Yau.Proofs.C01AffineCometricLevi

/-! Joint positivity of the actual cometric implies nonnegative
quadratic tangent curvature on every tested complex base line. -/

noncomputable section

open scoped Topology ContDiff Matrix ComplexOrder
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

theorem curvature_quadratic_nonneg_of_affine_dual {n : ℕ}
    (H : ℂ → Herm n) (s : Set ℂ) (hs : IsOpen s) (hzero : (0 : ℂ) ∈ s)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) s)
    (hpos : ∀ p ∈ s, (H p).PosDef)
    (hdual : ∀ ξ ν : Fin n → ℂ,
      0 ≤ (wirt (fun p => wirtBar (fun q : ℂ =>
        (dualNormMat (H q) (WithLp.toLp 2 (fun i => ξ i + q * ν i)) : ℂ)) p 1) 0 1).re) :
    let H₁ : Herm n := fun i j => wirt (fun p => H p i j) 0 1
    let H₂ : Herm n := fun i j => wirtBar (fun p => H p i j) 0 1
    let H₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => H q i j) p 1) 0 1
    ∀ v : Fin n → ℂ,
      0 ≤ (star v ⬝ᵥ ((-H₁₂ + H₂ * (H 0)⁻¹ * H₁) *ᵥ v)).re := by
  dsimp only
  let K := (H 0)⁻¹
  let H₁ : Herm n := fun i j => wirt (fun p => H p i j) 0 1
  let H₂ : Herm n := fun i j => wirtBar (fun p => H p i j) 0 1
  let H₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => H q i j) p 1) 0 1
  let K₁ : Herm n := fun i j => wirt (fun p => (H p)⁻¹ i j) 0 1
  let K₂ : Herm n := fun i j => wirtBar (fun p => (H p)⁻¹ i j) 0 1
  let K₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => (H q)⁻¹ i j) p 1) 0 1
  let C := -H₁₂ + H₂ * K * H₁
  have hdet (p : ℂ) (hp : p ∈ s) : (H p).det ≠ 0 :=
    ((hpos p hp).isUnit.map Matrix.detMonoidHom).ne_zero
  have hK (i j : Fin n) : ContDiffAt ℝ 2 (fun p => (H p)⁻¹ i j) 0 :=
    ((Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_inv hH hdet i j).contDiffAt
      (hs.mem_nhds hzero)).of_le (by simp)
  have hnorm (ξ ν : Fin n → ℂ) :
      (fun q : ℂ => (dualNormMat (H q)
        (WithLp.toLp 2 (fun i => ξ i + q * ν i)) : ℂ)) =ᶠ[𝓝 0]
      (fun q : ℂ => ∑ i, ∑ j,
        (ξ i + q * ν i) * (H q)⁻¹ i j * star (ξ j + q * ν j)) := by
    filter_upwards [hs.mem_nhds hzero] with p hp
    rw [dualNormMat_coe_eq_conjugate_quadratic (H p) (hpos p hp).isHermitian]
    simp only [star_star, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum,
      mul_assoc]
  have hjet (a b : Fin n → ℂ) :
      0 ≤ (star a ⬝ᵥ (K₁₂ *ᵥ a) + star b ⬝ᵥ (K₂ *ᵥ a) +
        star a ⬝ᵥ (K₁ *ᵥ b) + star b ⬝ᵥ (K *ᵥ b)).re := by
    have hp := hdual (star a) (star b)
    rw [wirt_wirtBar_congr_germ (hnorm (star a) (star b)) 1 1,
      affine_cometric_quadratic_mixed (fun p => (H p)⁻¹) hK] at hp
    simpa only [star_star] using hp
  have hschur : K₁₂ - K₁ * H 0 * K₂ = K * C * K :=
    matrix_inverse_mixed_schur H s hs hH hdet 0 1 1 hzero
  have hunit : IsUnit (H 0).det := (hpos 0 hzero).isUnit.map Matrix.detMonoidHom
  intro v
  have hquad := hjet (H 0 *ᵥ v) (-(H 0 *ᵥ (K₂ *ᵥ (H 0 *ᵥ v))))
  rw [free_jet_quadratic_elimination (H 0) K₁ K₂ K₁₂ hunit, hschur,
    inverse_metric_quadratic_cancel (H 0) C (hpos 0 hzero).isHermitian hunit] at hquad
  exact hquad

end Yau.NodeProofs.C01Aux
