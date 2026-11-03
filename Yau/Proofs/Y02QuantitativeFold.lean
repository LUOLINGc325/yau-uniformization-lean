import Yau.Proofs.Y02ShearFold
import Yau.Proofs.Y02QuantitativeStep

/-! An explicit finite recurrence for degree, coefficient prefactor and exponent. -/

noncomputable section

namespace Yau.Proofs.Y02Aux

variable {n : ℕ} {ι : Type*}

abbrev ShearBoundTriple := ℕ × ℝ × ℕ

def shearBoundStep (m E : ℕ) (a : ℝ) (b : ShearBoundTriple) : ShearBoundTriple :=
  (m * b.1,
    a * (1 + b.2.1) ^ m + b.2.1 * (1 + a) ^ b.1,
    max (E + m * b.2.2) (b.2.2 + E * b.1))

def shearBounds (m E : ℕ) (a : ℝ) : List ι → ShearBoundTriple → ShearBoundTriple
  | [], b => b
  | _ :: L, b => shearBounds m E a L (shearBoundStep m E a b)

theorem shearBoundStep_lower (m E : ℕ) (a : ℝ) (b : ShearBoundTriple)
    (hm : 1 ≤ m) (hE : 1 ≤ E) (ha : 1 ≤ a)
    (hD : 1 ≤ b.1) (hK : 1 ≤ b.2.1) (_he : 1 ≤ b.2.2) :
    1 ≤ (shearBoundStep m E a b).1 ∧ 1 ≤ (shearBoundStep m E a b).2.1 ∧
      1 ≤ (shearBoundStep m E a b).2.2 := by
  dsimp [shearBoundStep]
  refine ⟨one_le_mul_of_one_le_of_one_le hm hD, ?_, ?_⟩
  · have hp : 1 ≤ (1 + b.2.1) ^ m := one_le_pow₀ (by linarith)
    have hfirst : 1 ≤ a * (1 + b.2.1) ^ m := one_le_mul_of_one_le_of_one_le ha hp
    have hsecond : 0 ≤ b.2.1 * (1 + a) ^ b.1 := by positivity
    linarith
  · exact hE.trans ((Nat.le_add_right E (m * b.2.2)).trans (le_max_left _ _))

theorem shearBounds_lower (m E : ℕ) (a : ℝ) (L : List ι) (b : ShearBoundTriple)
    (hm : 1 ≤ m) (hE : 1 ≤ E) (ha : 1 ≤ a)
    (hD : 1 ≤ b.1) (hK : 1 ≤ b.2.1) (he : 1 ≤ b.2.2) :
    1 ≤ (shearBounds m E a L b).1 ∧ 1 ≤ (shearBounds m E a L b).2.1 ∧
      1 ≤ (shearBounds m E a L b).2.2 := by
  induction L generalizing b with
  | nil => exact ⟨hD, hK, he⟩
  | cons t L ih =>
    obtain ⟨hD', hK', he'⟩ := shearBoundStep_lower m E a b hm hE ha hD hK he
    exact ih (shearBoundStep m E a b) hD' hK' he'

theorem shearFold_bound (l v : ι → Fin n → ℂ) {m : ℕ} (hm : 2 ≤ m)
    (c : ι → ℂ) (L : List ι) (E : ℕ) (a t : ℝ) (ht : 1 ≤ t) (ha : 0 ≤ a)
    (hS : ∀ i, (shear (l i) (v i) m (c i)).coeffNorm ≤ a * t ^ E)
    (hT : ∀ i, (shear (l i) (v i) m (-c i)).coeffNorm ≤ a * t ^ E)
    (b : ShearBoundTriple) (hk : 0 ≤ b.2.1) (G Ginv : PolyMap n)
    (hG : G.degree ≤ b.1) (hGinv : Ginv.degree ≤ b.1)
    (hnorm : G.coeffNorm + Ginv.coeffNorm ≤ b.2.1 * t ^ b.2.2) :
    (shearFoldForward l v m c L G).degree ≤ (shearBounds m E a L b).1 ∧
      (shearFoldInverse l v m c L Ginv).degree ≤ (shearBounds m E a L b).1 ∧
      (shearFoldForward l v m c L G).coeffNorm + (shearFoldInverse l v m c L Ginv).coeffNorm ≤
        (shearBounds m E a L b).2.1 * t ^ (shearBounds m E a L b).2.2 := by
  induction L generalizing b G Ginv with
  | nil => exact ⟨hG, hGinv, hnorm⟩
  | cons i L ih =>
    have hSi : (shear (l i) (v i) m (c i)).degree ≤ m :=
      (shear_degree_le _ _ _ _).trans (max_le (by omega) le_rfl)
    have hTi : (shear (l i) (v i) m (-c i)).degree ≤ m :=
      (shear_degree_le _ _ _ _).trans (max_le (by omega) le_rfl)
    have hDnew : ((shear (l i) (v i) m (c i)).comp G).degree ≤ m * b.1 :=
      (comp_degree_le _ _).trans (Nat.mul_le_mul hSi hG)
    have hDinvnew : (Ginv.comp (shear (l i) (v i) m (-c i))).degree ≤ m * b.1 := by
      apply (comp_degree_le _ _).trans
      simpa only [Nat.mul_comm b.1 m] using Nat.mul_le_mul hGinv hTi
    have hnormnew := shear_pair_bound_step (shear (l i) (v i) m (c i))
      (shear (l i) (v i) m (-c i)) G Ginv m b.1 E b.2.2 a b.2.1 t
      ht ha hk hSi hG hGinv (hS i) (hT i) hnorm
    have hknew : 0 ≤ (shearBoundStep m E a b).2.1 := by dsimp [shearBoundStep]; positivity
    exact ih (shearBoundStep m E a b) hknew
      ((shear (l i) (v i) m (c i)).comp G) (Ginv.comp (shear (l i) (v i) m (-c i)))
      hDnew hDinvnew hnormnew

theorem shear_coeffNorm_le (l v : Fin n → ℂ) (m : ℕ) (c : ℂ) :
    (shear l v m c).coeffNorm ≤ (n : ℝ) + ‖c‖ * (shearField l v m).coeffNorm := by
  rw [shear_eq_id_add]
  simpa only [coeffNorm_id, coeffNorm_smul] using coeffNorm_add_le PolyMap.id (c • shearField l v m)

end Yau.Proofs.Y02Aux
