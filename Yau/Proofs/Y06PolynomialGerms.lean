import Yau.Proofs.Y01PolynomialJets
import Yau.Proofs.Y01JetNormExtraction

/-! Polynomial jets and actual Fréchet jets agree in both directions.
This permits coefficient compactness without taking limits of derivatives. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux
open scoped ContDiff

variable {n d : ℕ}

theorem polynomial_eval_sub (P Q : PolyMap n) : (P - Q).eval = P.eval - Q.eval := by
  funext z
  ext i
  exact map_sub (MvPolynomial.eval (fun j => z j)) (P i) (Q i)

theorem germJetEq_polynomial_jetEq {P Q : PolyMap n} (h : GermJetEq P.eval Q.eval d) :
    PolyMap.JetEq P Q d := by
  intro i β hβ
  change β.degree ≤ d at hβ
  have hderiv : iteratedFDeriv ℂ β.degree (P - Q).eval 0 = 0 := by
    rw [polynomial_eval_sub, iteratedFDeriv_sub_apply
      ((polyMap_eval_contDiff P).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      ((polyMap_eval_contDiff Q).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
      h β.degree hβ, sub_self]
  have hbound := (scalar_coeff_norm_le_jet ((P - Q) i) β).trans
    (scalar_projection_jet_norm (P - Q) i β.degree)
  rw [hderiv, norm_zero] at hbound
  have hz := norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))
  change (P i).coeff β - (Q i).coeff β = 0 at hz
  exact sub_eq_zero.mp hz

theorem polynomial_germJetEq_iff {P Q : PolyMap n} :
    GermJetEq P.eval Q.eval d ↔ PolyMap.JetEq P Q d :=
  ⟨germJetEq_polynomial_jetEq, jetEq_germJetEq⟩

end Yau.Proofs.Y06Aux
