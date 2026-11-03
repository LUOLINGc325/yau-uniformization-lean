import Yau.Proofs.P03NakanoLeviAlgebra
import Yau.LeafProofs.L07
import Mathlib.Analysis.Matrix.Hermitian

open scoped Matrix ComplexOrder

noncomputable section

namespace Yau.NodeProofs.P03Aux

open Yau.BundleDbar Yau.LeafProofs

/-- A lower bound on the genuine Hermitian quadratic is exactly the
semidefiniteness of the corresponding real scalar matrix difference. -/
theorem matrix_sub_real_smul_posSemidef {m : ℕ}
    (L G : Matrix (Fin m) (Fin m) ℂ) (hL : L.IsHermitian) (hG : G.IsHermitian)
    (t : ℝ) (hbound : ∀ v : Fin m → ℂ,
      t * (star v ⬝ᵥ (G *ᵥ v)).re ≤ (star v ⬝ᵥ (L *ᵥ v)).re) :
    (L - (t : ℂ) • G).PosSemidef := by
  have ht : IsSelfAdjoint (t : ℂ) := by simp [IsSelfAdjoint]
  have hH : (L - (t : ℂ) • G).IsHermitian := hL.sub (hG.smul ht)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  apply Complex.nonneg_iff.mpr
  constructor
  · simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact sub_nonneg.mpr (hbound v)
  · exact (hH.im_star_dotProduct_mulVec_self v).symm

theorem nakano_leviCorrection_sub_real (L G : Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (U : Fin n → Fin r → ℂ) :
    nakanoQuadratic (fun i j => (L - (t : ℂ) • G) j i • H) U =
      nakanoQuadratic (fun i j => L j i • H) U -
        t * nakanoQuadratic (fun i j => G j i • H) U := by
  have he : (fun i j => (L - (t : ℂ) • G) j i • H) =
      (fun i j => L j i • H + (-t : ℂ) • (G j i • H)) := by
    funext i j
    ext α β
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
    ring
  rw [he, nakanoQuadratic_add, L07Aux.nakanoQuadratic_smul_real
    (fun i j => G j i • H) (-t : ℂ) (by simp)]
  simp only [Complex.neg_re, Complex.ofReal_re]
  ring

theorem nakano_leviCorrection_relative_lower (L G : Matrix (Fin n) (Fin n) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hLG : (L - (t : ℂ) • G).PosSemidef) (hH : H.PosSemidef)
    (U : Fin n → Fin r → ℂ) :
    t * nakanoQuadratic (fun i j => G j i • H) U ≤
      nakanoQuadratic (fun i j => L j i • H) U := by
  have hn := nakano_leviCorrection_nonnegative hLG hH U
  rw [nakano_leviCorrection_sub_real] at hn
  linarith

end Yau.NodeProofs.P03Aux
