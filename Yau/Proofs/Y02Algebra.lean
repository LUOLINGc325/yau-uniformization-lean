import Yau.Geometry.Polynomial

/-! Algebra of the polynomial shears used to realize volume jets. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

open MvPolynomial

variable {n : ℕ}

theorem comp_id (P : PolyMap n) : P.comp PolyMap.id = P := by
  funext i
  change bind₁ X (P i) = P i
  rw [bind₁_X_left]
  rfl

theorem id_comp (P : PolyMap n) : PolyMap.id.comp P = P := by
  funext i
  simp [PolyMap.comp, PolyMap.id]

theorem comp_assoc (P Q R : PolyMap n) : (P.comp Q).comp R = P.comp (Q.comp R) := by
  funext i
  exact bind₁_bind₁ Q R (P i)

theorem automorphism_id : IsPolyAutomorphism (PolyMap.id : PolyMap n) PolyMap.id :=
  ⟨comp_id _, comp_id _⟩

theorem automorphism_comp {P Pinv Q Qinv : PolyMap n}
    (hP : IsPolyAutomorphism P Pinv) (hQ : IsPolyAutomorphism Q Qinv) :
    IsPolyAutomorphism (P.comp Q) (Qinv.comp Pinv) := by
  constructor
  · rw [comp_assoc, ← comp_assoc Q, hQ.1, id_comp, hP.1]
  · rw [comp_assoc, ← comp_assoc Pinv, hP.2, id_comp, hQ.2]

theorem jetEq_refl (P : PolyMap n) (d : ℕ) : PolyMap.JetEq P P d := by
  intro i m hm
  rfl

theorem jetEq_symm {P Q : PolyMap n} {d : ℕ} (h : PolyMap.JetEq P Q d) :
    PolyMap.JetEq Q P d := by
  intro i m hm
  exact (h i m hm).symm

theorem jetEq_trans {P Q R : PolyMap n} {d : ℕ}
    (hPQ : PolyMap.JetEq P Q d) (hQR : PolyMap.JetEq Q R d) :
    PolyMap.JetEq P R d := by
  intro i m hm
  exact (hPQ i m hm).trans (hQR i m hm)

theorem coeffNorm_nonneg (P : PolyMap n) : 0 ≤ P.coeffNorm := by
  unfold PolyMap.coeffNorm
  positivity

/-- The linear form defining a shear direction. -/
def linearForm (l : Fin n → ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (l j) * X j

/-- The time-`c` map of the homogeneous shear vector field `l^m v`. -/
def shear (l v : Fin n → ℂ) (m : ℕ) (c : ℂ) : PolyMap n :=
  fun i => X i + C (c * v i) * linearForm l ^ m

theorem bind_linearForm (l : Fin n → ℂ) (P : PolyMap n) :
    bind₁ P (linearForm l) = ∑ j, C (l j) * P j := by
  simp [linearForm]

theorem linearForm_shear (l v : Fin n → ℂ) (m : ℕ) (c : ℂ)
    (hlv : ∑ j, l j * v j = 0) :
    bind₁ (shear l v m c) (linearForm l) = linearForm l := by
  rw [bind_linearForm]
  simp only [shear, mul_add, Finset.sum_add_distrib]
  change linearForm l + (∑ j, C (l j) * (C (c * v j) * linearForm l ^ m)) = _
  have hzero : (∑ j, C (l j) * (C (c * v j) * linearForm l ^ m)) = 0 := by
    calc
      _ = (∑ j, C (c * (l j * v j))) * linearForm l ^ m := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        rw [← mul_assoc, ← map_mul]
        congr 2
        ring
      _ = C (c * ∑ j, l j * v j) * linearForm l ^ m := by
        rw [Finset.mul_sum, map_sum]
      _ = 0 := by rw [hlv]; simp
  rw [hzero, add_zero]

theorem shear_comp (l v : Fin n → ℂ) (m : ℕ) (c e : ℂ)
    (hlv : ∑ j, l j * v j = 0) :
    (shear l v m c).comp (shear l v m e) = shear l v m (c + e) := by
  funext i
  simp only [PolyMap.comp, shear, map_add, bind₁_X_right, map_mul,
    bind₁_C_right, map_pow]
  rw [linearForm_shear l v m e hlv]
  ring

theorem shear_zero (l v : Fin n → ℂ) (m : ℕ) : shear l v m 0 = PolyMap.id := by
  funext i
  simp [shear, PolyMap.id]

/-- The inverse shear is the time map with the opposite coefficient. -/
theorem shear_automorphism (l v : Fin n → ℂ) (m : ℕ) (c : ℂ)
    (hlv : ∑ j, l j * v j = 0) :
    IsPolyAutomorphism (shear l v m c) (shear l v m (-c)) := by
  constructor
  · rw [shear_comp l v m c (-c) hlv, add_neg_cancel, shear_zero]
  · rw [shear_comp l v m (-c) c hlv, neg_add_cancel, shear_zero]

end Yau.Proofs.Y02Aux
