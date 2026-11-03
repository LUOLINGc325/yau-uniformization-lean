import Yau.Proofs.Y06SubstitutionDifference
import Yau.Proofs.Y06HomogeneousAlgebra
import Yau.Proofs.Y06StrictWeight

/-! The complete homogeneous layer equation advances the whole jet
identity, including the allowed coefficients. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n m : ℕ}

theorem linearPolynomial_comp_add (A : Herm n) (P Q : PolyMap n) :
    (linearPolynomial A).comp (P + Q) = (linearPolynomial A).comp P + (linearPolynomial A).comp Q := by
  funext i
  change (linearPoly A).comp (P + Q) i = (linearPoly A).comp P i + (linearPoly A).comp Q i
  simp only [linearPoly_comp_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem homogeneous_comp_same_linear {P : PolyMap n} (hP : Homogeneous P m)
    (U V : PolyMap n) (hU : U.FixesZero) (hV : V.FixesZero)
    (hUV : mapOrderAtLeast 2 (U - V)) : PolyMap.JetEq (P.comp U) (P.comp V) m := by
  rw [jetEq_iff_order]
  intro i
  change scalarOrderAtLeast (m + 1) (bind₁ U (P i) - bind₁ V (P i))
  apply scalarOrderAtLeast_mono
    (scalar_bind_difference_order (by norm_num : 1 ≤ 2) U V hU hV hUV (P i) (homogeneous_order hP i))
  omega

theorem nonlinear_comp_update {G H u : PolyMap n} (hm : 2 ≤ m)
    (hG : G.FixesZero) (hH : H.FixesZero) (hu : Homogeneous u m) :
    PolyMap.JetEq ((nonlinearPart G).comp (H + u)) ((nonlinearPart G).comp H) m := by
  have hu0 := homogeneous_fixesZero hu (by omega)
  have hdiff : mapOrderAtLeast m ((H + u) - H) := by
    have heq : (H + u) - H = u := by abel
    rw [heq]
    exact homogeneous_order hu
  rw [jetEq_iff_order]
  intro i
  change scalarOrderAtLeast (m + 1)
    (bind₁ (H + u) (nonlinearPart G i) - bind₁ H (nonlinearPart G i))
  apply scalarOrderAtLeast_mono
    (scalar_bind_difference_order (by omega : 1 ≤ m) (H + u) H
      (polynomial_fixesZero_add hH hu0) hH hdiff (nonlinearPart G i) (nonlinearPart_order_two hG i))
  omega

theorem first_order_composition_update {G H u : PolyMap n} (D : Herm n) (hm : 2 ≤ m)
    (hG : G.FixesZero) (hD : G.linearPart = D) (hH : H.FixesZero) (hu : Homogeneous u m) :
    PolyMap.JetEq (G.comp (H + u)) (G.comp H + (linearPolynomial D).comp u) m := by
  have hsplit : G = linearPolynomial D + nonlinearPart G := by
    rw [← hD]
    change G = linearPolynomial G.linearPart + (G - linearPolynomial G.linearPart)
    abel
  have hnew : G.comp (H + u) =
      ((linearPolynomial D).comp H + (linearPolynomial D).comp u) + (nonlinearPart G).comp (H + u) := by
    rw [show G.comp (H + u) = (linearPolynomial D + nonlinearPart G).comp (H + u) from
      congrArg (fun P : PolyMap n => P.comp (H + u)) hsplit,
      Yau.Proofs.Y02Aux.comp_add_left, linearPolynomial_comp_add]
  have hold : G.comp H = (linearPolynomial D).comp H + (nonlinearPart G).comp H := by
    rw [show G.comp H = (linearPolynomial D + nonlinearPart G).comp H from
      congrArg (fun P : PolyMap n => P.comp H) hsplit, Yau.Proofs.Y02Aux.comp_add_left]
  rw [hnew, hold]
  intro i β hβ
  have hnonlinear := nonlinear_comp_update hm hG hH hu i β hβ
  change ((linearPolynomial D).comp H i).coeff β + ((linearPolynomial D).comp u i).coeff β +
    ((nonlinearPart G).comp (H + u) i).coeff β =
      (((linearPolynomial D).comp H i).coeff β + ((nonlinearPart G).comp H i).coeff β) +
        ((linearPolynomial D).comp u i).coeff β
  rw [hnonlinear]
  ring

theorem complete_composition_layer_update {G H u v : PolyMap n} (D : Herm n) (hm : 2 ≤ m)
    (hG : G.FixesZero) (hD : G.linearPart = D) (hH : tangentId H)
    (hu : Homogeneous u m) (hv : Homogeneous v m) :
    PolyMap.JetEq ((G + v).comp (H + u)) (G.comp H + (linearPolynomial D).comp u + v) m := by
  have hu0 := homogeneous_fixesZero hu (by omega)
  have hHu : tangentId (H + u) := by
    refine ⟨polynomial_fixesZero_add hH.1 hu0, ?_⟩
    rw [polynomial_linearPart_add, hH.2, homogeneous_linearPart_zero hu (by omega), add_zero]
  have hvjet : PolyMap.JetEq (v.comp (H + u)) v m := by
    rw [jetEq_iff_order]
    intro i
    exact homogeneous_bind_sub_order (H + u) hHu (v i) ((homogeneous_iff_components _).mp hv i)
  rw [Yau.Proofs.Y02Aux.comp_add_left]
  exact jetEq_add (first_order_composition_update D hm hG hD hH.1 hu) hvjet

end Yau.Proofs.Y06Aux
