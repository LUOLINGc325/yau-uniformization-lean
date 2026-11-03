import Yau.Proofs.Y02CompositionBounds
import Yau.Proofs.Y02JetExtraction

/-! Fixed numerical bounds for one forward and inverse shear update. -/

noncomputable section

namespace Yau.Proofs.Y02Aux

variable {n : ℕ}

theorem one_add_mul_pow_le {b t : ℝ} (ht : 1 ≤ t) (s : ℕ) :
    1 + b * t ^ s ≤ (1 + b) * t ^ s := by
  have hp : 1 ≤ t ^ s := one_le_pow₀ ht
  nlinarith

theorem composition_bound_le (P Q : PolyMap n) {D : ℕ} (hD : P.degree ≤ D)
    {A B : ℝ} (hA : P.coeffNorm ≤ A) (hB : Q.coeffNorm ≤ B) :
    (P.comp Q).coeffNorm ≤ A * (1 + B) ^ D := by
  have hAn : 0 ≤ A := (coeffNorm_nonneg P).trans hA
  have hBn : 0 ≤ B := (coeffNorm_nonneg Q).trans hB
  apply (comp_coeffNorm_le P Q).trans
  have hpowers : (1 + Q.coeffNorm) ^ P.degree ≤ (1 + B) ^ D :=
    (pow_le_pow_left₀ (by linarith [coeffNorm_nonneg Q]) (by linarith) P.degree).trans
      (pow_le_pow_right₀ (by linarith) hD)
  exact mul_le_mul hA hpowers (pow_nonneg (by linarith [coeffNorm_nonneg Q]) _) hAn

theorem shear_pair_bound_step (S T G Ginv : PolyMap n) (m D E e : ℕ) (a k t : ℝ)
    (ht : 1 ≤ t) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hSdegree : S.degree ≤ m) (_hGdegree : G.degree ≤ D) (hGinvdegree : Ginv.degree ≤ D)
    (hSnorm : S.coeffNorm ≤ a * t ^ E) (hTnorm : T.coeffNorm ≤ a * t ^ E)
    (hGnorm : G.coeffNorm + Ginv.coeffNorm ≤ k * t ^ e) :
    (S.comp G).coeffNorm + (Ginv.comp T).coeffNorm ≤
      (a * (1 + k) ^ m + k * (1 + a) ^ D) * t ^ max (E + m * e) (e + E * D) := by
  have htn : 0 ≤ t := zero_le_one.trans ht
  have hGn : G.coeffNorm ≤ k * t ^ e := by linarith [coeffNorm_nonneg Ginv]
  have hGinvn : Ginv.coeffNorm ≤ k * t ^ e := by linarith [coeffNorm_nonneg G]
  have hforward : (S.comp G).coeffNorm ≤ a * (1 + k) ^ m * t ^ (E + m * e) := by
    calc
      _ ≤ (a * t ^ E) * (1 + k * t ^ e) ^ m :=
        composition_bound_le S G hSdegree hSnorm hGn
      _ ≤ (a * t ^ E) * ((1 + k) * t ^ e) ^ m := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        exact one_add_mul_pow_le ht e
      _ = _ := by rw [mul_pow, pow_add, Nat.mul_comm m e, pow_mul]; ring
  have hbackward : (Ginv.comp T).coeffNorm ≤ k * (1 + a) ^ D * t ^ (e + E * D) := by
    calc
      _ ≤ (k * t ^ e) * (1 + a * t ^ E) ^ D :=
        composition_bound_le Ginv T hGinvdegree hGinvn hTnorm
      _ ≤ (k * t ^ e) * ((1 + a) * t ^ E) ^ D := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        exact one_add_mul_pow_le ht E
      _ = _ := by rw [mul_pow, pow_add, pow_mul]; ring
  have hf := (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ht (le_max_left (E + m * e) (e + E * D)))
    (by positivity : 0 ≤ a * (1 + k) ^ m))
  have hb := (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ht (le_max_right (E + m * e) (e + E * D)))
    (by positivity : 0 ≤ k * (1 + a) ^ D))
  calc
    _ ≤ a * (1 + k) ^ m * t ^ max (E + m * e) (e + E * D) +
        k * (1 + a) ^ D * t ^ max (E + m * e) (e + E * D) :=
      add_le_add (hforward.trans hf) (hbackward.trans hb)
    _ = _ := by ring

end Yau.Proofs.Y02Aux
