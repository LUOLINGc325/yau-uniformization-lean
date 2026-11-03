import Yau.LeafProofs.L23CurvatureReaction
import Yau.LeafProofs.L23MetricMixedTime

/-! The Ricci covariant derivatives in the original time-variation formula. -/

noncomputable section
open scoped Topology ContDiff

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : ComplexManifold n}

theorem realRicciCoeff_symm (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j : RIdx n) :
    realRicciCoeff h c z i j=realRicciCoeff h c z j i := by
  rw [realRicciCoeff_eq_realRicciMatrix h c z hz,
    realRicciCoeff_eq_realRicciMatrix h c z hz]
  exact realRicciMatrix_symm h hh c z hz i j

theorem covariantD_ricciTensor_three (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (i j q : RIdx n) :
    covariantD h c (ricciTensor h c) z ![i,j,q]=
      rDeriv (fun w => realRicciCoeff h c w j q) z i-
        (∑ p, christoffel h c z p i j*realRicciCoeff h c z p q)-
        ∑ p, christoffel h c z p i q*realRicciCoeff h c z j p := by
  simp [covariantD,ricciTensor,Fin.sum_univ_succ]
  ring

theorem ricciDerivative_koszul_combination (h : HermitianField M) (hh : MetricSmooth h)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) (i j q : RIdx n) :
    covariantD h c (ricciTensor h c) z ![i,j,q]+
      covariantD h c (ricciTensor h c) z ![j,i,q]-
        covariantD h c (ricciTensor h c) z ![q,i,j]=
      rDeriv (fun w => realRicciCoeff h c w j q) z i+
        rDeriv (fun w => realRicciCoeff h c w i q) z j-
          rDeriv (fun w => realRicciCoeff h c w i j) z q-
            2*∑ p, christoffel h c z p i j*realRicciCoeff h c z p q := by
  simp only [covariantD_ricciTensor_three]
  have h1 : (∑ p, christoffel h c z p j i*realRicciCoeff h c z p q)=
      ∑ p, christoffel h c z p i j*realRicciCoeff h c z p q := by
    simp only [L12Aux.christoffel_symm_lower h c z (a := j) (b := i)]
  have h2 : (∑ p, christoffel h c z p q i*realRicciCoeff h c z p j)=
      ∑ p, christoffel h c z p i q*realRicciCoeff h c z j p := by
    apply Finset.sum_congr rfl
    intro p _
    rw [L12Aux.christoffel_symm_lower h c z (a := q) (b := i),
      realRicciCoeff_symm h hh c hz p j]
  have h3 : (∑ p, christoffel h c z p q j*realRicciCoeff h c z i p)=
      ∑ p, christoffel h c z p j q*realRicciCoeff h c z i p := by
    simp only [L12Aux.christoffel_symm_lower h c z (a := q) (b := j)]
  rw [h1,h2,h3]
  ring

end Yau.LeafProofs.L23Aux
