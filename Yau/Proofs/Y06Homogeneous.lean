import Yau.Proofs.Y06ForbiddenProjection

/-! Linear substitutions preserve every homogeneous layer of the original
operator. No forbidden support condition is imposed on the input layer. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux

variable {n m : ℕ}

theorem homogeneous_iff_components (P : PolyMap n) :
    Homogeneous P m ↔ ∀ i, (P i).IsHomogeneous m := by
  constructor
  · intro h i β hβ
    change Finsupp.weight (fun _ : Fin n => 1) β = m
    rw [← Finsupp.degree_eq_weight_one]
    exact h i β hβ
  · intro h i β hβ
    change β.degree = m
    rw [Finsupp.degree_eq_weight_one]
    exact h i hβ

theorem homogeneous_comp_linear {P : PolyMap n} (hP : Homogeneous P m) (A : Herm n) :
    Homogeneous (P.comp (linearPolynomial A)) m := by
  apply (homogeneous_iff_components _).mpr
  have hcomp := (homogeneous_iff_components P).mp hP
  intro i
  have hs := (hcomp i).eval₂ (C : ℂ →+* MvPolynomial (Fin n) ℂ)
    (linearPolynomial A) (fun c => isHomogeneous_C _ c) (fun j => linearForm_homogeneous (A j))
  simpa only [one_mul, PolyMap.comp, bind₁, aeval_def, algebraMap_eq] using hs

theorem homogeneous_linear_comp {P : PolyMap n} (hP : Homogeneous P m) (A : Herm n) :
    Homogeneous ((linearPolynomial A).comp P) m := by
  apply (homogeneous_iff_components _).mpr
  have hcomp := (homogeneous_iff_components P).mp hP
  intro i
  change ((linearPoly A).comp P i).IsHomogeneous m
  rw [linearPoly_comp_apply]
  exact IsHomogeneous.sum _ _ _ (fun j hj => (hcomp j).C_mul (A i j))

theorem backwardOperator_homogeneous (D J : Herm n) (w : Fin n → ℝ)
    {P : PolyMap n} (hP : Homogeneous P m) : Homogeneous (backwardOperator D J w P) m := by
  apply forbiddenProjection_homogeneous
  exact homogeneous_linear_comp (homogeneous_linear_comp
    (homogeneous_comp_linear hP (J * D)) J⁻¹) D⁻¹

theorem homogeneous_degree_le {P : PolyMap n} (hP : Homogeneous P m) : P.degree ≤ m := by
  unfold PolyMap.degree
  apply Finset.sup_le
  intro i hi
  exact ((homogeneous_iff_components P).mp hP i).totalDegree_le

end Yau.Proofs.Y06Aux
