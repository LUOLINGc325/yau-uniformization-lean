import Yau.Proofs.F05BootstrapGoodQuotient
import Yau.Proofs.F05BootstrapTemporalQuotientEquation

/-! Literal endpoint identities for the actual good quotients. -/

noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

theorem F05_good_quotient_spatial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (j : RIdx n) (h : ℝ) (u : Point n → V) :
    F05GoodQuotient (some j) h u = spatialDifferenceQuotient u (realVec j) h := by
  funext z
  simp only [F05GoodQuotient,F05GoodSegment,spatialDifferenceQuotient,one_mul,zero_mul,zero_smul,add_zero,Prod.eta]

theorem F05_good_quotient_temporal (h : ℝ) (u : Point n → ℝ) :
    F05GoodQuotient none h u = F05BackwardTimeQuotient u h := by
  funext z
  simp only [F05GoodQuotient,F05GoodSegment,F05BackwardTimeQuotient,timeTranslate,timeTranslatePoint,
    one_mul,zero_mul,add_zero,sub_add_cancel,smul_eq_mul,Prod.eta,sub_eq_add_neg,neg_add_cancel_right]

end Yau.Proofs.F05Aux
