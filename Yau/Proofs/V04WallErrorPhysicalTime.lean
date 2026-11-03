import Yau.Proofs.V04WallErrorInverseTime
import Yau.Proofs.V03MetricTime

/-! The physical time derivative of the genuine dual norm, including zero.
Only the original Kähler–Ricci flow derivative within `Ici 0` is used. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem krf_inverseMetric_hasDerivWithinAt
    {g : HermitianField M} {h : ℝ → HermitianField M}
    (hh : IsKahlerRicciFlow g h) (x : M.Carrier) {t : ℝ} (ht : 0 ≤ t)
    (i j : Fin n) :
    HasDerivWithinAt (fun s => (gMat (h s) x)⁻¹ i j)
      (((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹) i j) (Set.Ici 0) t := by
  have hm := matrix_inverse_hasDerivWithinAt_of_entries (S := Set.Ici 0) ht (uniqueDiffOn_Ici 0 t ht)
    (A := fun s => gMat (h s) x) (D := -ricci (h t) x)
    (fun i j => hh.2.2.2 x t ht i j)
    (fun s _ => (gMat_posDef (h s) x).isUnit.map Matrix.detMonoidHom) i j
  simpa only [Matrix.neg_mul, Matrix.mul_neg, neg_neg] using hm

theorem krf_dualNorm_hasDerivWithinAt
    {g : HermitianField M} {h : ℝ → HermitianField M}
    (hh : IsKahlerRicciFlow g h) (x : M.Carrier) (ξ : Covector n)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => dualNorm (h s) x ξ)
      (star (WithLp.ofLp (covectorCoords x x ξ)) ⬝ᵥ
        (((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹)ᵀ *ᵥ
          WithLp.ofLp (covectorCoords x x ξ))).re (Set.Ici 0) t := by
  let v := WithLp.ofLp (covectorCoords x x ξ)
  have hq : HasDerivWithinAt
      (fun s => ∑ i, star (v i) * ∑ j, (gMat (h s) x)⁻¹ j i * v j)
      (∑ i, star (v i) * ∑ j,
        ((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹) j i * v j)
      (Set.Ici 0) t := by
    apply HasDerivWithinAt.fun_sum
    intro i _
    apply HasDerivWithinAt.const_mul
    apply HasDerivWithinAt.fun_sum
    intro j _
    exact (krf_inverseMetric_hasDerivWithinAt hh x ht j i).mul_const (v j)
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hq

theorem krf_dualNorm_derivWithin
    {g : HermitianField M} {h : ℝ → HermitianField M}
    (hh : IsKahlerRicciFlow g h) (x : M.Carrier) (ξ : Covector n)
    {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (fun s => dualNorm (h s) x ξ) (Set.Ici 0) t =
      (star (WithLp.ofLp (covectorCoords x x ξ)) ⬝ᵥ
        (((gMat (h t) x)⁻¹ * ricci (h t) x * (gMat (h t) x)⁻¹)ᵀ *ᵥ
          WithLp.ofLp (covectorCoords x x ξ))).re :=
  (krf_dualNorm_hasDerivWithinAt hh x ξ ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

end Yau.Blueprint.V04Proof.WallErrorAux
