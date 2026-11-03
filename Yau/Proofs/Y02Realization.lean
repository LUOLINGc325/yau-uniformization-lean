import Yau.Proofs.Y02NormalizedRealization
import Yau.Proofs.Y02Normalization
import Yau.Blueprint.Nodes

/-! Realization of the original constant-volume jets with uniform raw bounds. -/

noncomputable section

namespace Yau.Proofs.Y02Aux

open Yau.Blueprint

theorem volumeJets_proved (n d : ℕ) (hd : 2 ≤ d) : VolumeJets n d := by
  obtain ⟨D, K, E, hD, hK, hE, hrealize⟩ := normalized_volume_realization n d (by omega)
  let q : ℝ := 1 + (n : ℝ) ^ 2
  have hq : 1 ≤ q := by dsimp [q]; nlinarith [sq_nonneg (n : ℝ)]
  let W : ℝ := K * q ^ E
  have hW : 0 ≤ W := mul_nonneg (zero_le_one.trans hK) (pow_nonneg (zero_le_one.trans hq) _)
  let Er : ℕ := 2 * E + D
  let Kr : ℝ := (1 + W) + W * q ^ D
  let C : ℝ := max 1 (max Kr (Er : ℝ))
  have hC : 1 ≤ C := le_max_left _ _
  have hKrC : Kr ≤ C := (le_max_left Kr (Er : ℝ)).trans (le_max_right _ _)
  have hErC : (Er : ℝ) ≤ C := (le_max_right Kr (Er : ℝ)).trans (le_max_right _ _)
  refine ⟨D, C, ?_⟩
  intro J hJ
  have hnormalized := normalize_constantVolumeJet J hJ
  let P := normalizedJet J
  have hPflat : positiveJacFlat P d := hnormalized.2.1.2.2.2
  obtain ⟨G, Ginv, hpair, _hG, _hGinv, _hdet, _hdetinv, hjet, hdeg, hdeginv, hnorm⟩ :=
    hrealize P hnormalized.1 hPflat
  let F := (linearPoly J.linearPart).comp G
  let Finv := Ginv.comp (linearPoly J.linearPart⁻¹)
  have hFpair : IsPolyAutomorphism F Finv :=
    automorphism_comp (linearPoly_automorphism J.linearPart hJ.2.2.1) hpair
  have hFjet : PolyMap.JetEq F J d := by
    have h := jetEq_linearPoly_comp J.linearPart hjet
    rwa [hnormalized.2.2.1] at h
  have hFdegree : F.degree ≤ D := by
    apply (comp_degree_le _ _).trans
    simpa only [one_mul] using Nat.mul_le_mul (linearPoly_degree_le J.linearPart) hdeg
  have hFinvdegree : Finv.degree ≤ D := by
    apply (comp_degree_le _ _).trans
    simpa only [mul_one] using Nat.mul_le_mul hdeginv (linearPoly_degree_le J.linearPart⁻¹)
  refine ⟨F, Finv, hFpair, hFjet, hFdegree, hFinvdegree, ?_⟩
  let S : ℝ := 1 + J.coeffNorm + matOpNorm J.linearPart⁻¹
  have hinv : 0 ≤ matOpNorm J.linearPart⁻¹ := by unfold matOpNorm; exact norm_nonneg _
  have hS : 1 ≤ S := by dsimp [S]; linarith [coeffNorm_nonneg J]
  have hSn : 0 ≤ S := zero_le_one.trans hS
  have hJle : J.coeffNorm ≤ S := by dsimp [S]; linarith
  have hInvle : matOpNorm J.linearPart⁻¹ ≤ S := by dsimp [S]; linarith [coeffNorm_nonneg J]
  have hPNorm : 1 + P.coeffNorm ≤ q * S ^ 2 :=
    (normalizedJet_coeffNorm_le_square J hJ).2.2
  have hGsum : G.coeffNorm + Ginv.coeffNorm ≤ W * S ^ (2 * E) := by
    calc
      _ ≤ K * (1 + P.coeffNorm) ^ E := hnorm
      _ ≤ K * (q * S ^ 2) ^ E := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith [coeffNorm_nonneg P]) hPNorm E) (zero_le_one.trans hK)
      _ = _ := by dsimp [W]; rw [mul_pow, pow_mul]; ring
  have hGn : G.coeffNorm ≤ W * S ^ (2 * E) := by linarith [coeffNorm_nonneg Ginv]
  have hGinvn : Ginv.coeffNorm ≤ W * S ^ (2 * E) := by linarith [coeffNorm_nonneg G]
  have hLin : (linearPoly J.linearPart).coeffNorm ≤ S :=
    (linearPoly_linearPart_coeffNorm_le J).trans hJle
  have hLinInv : (linearPoly J.linearPart⁻¹).coeffNorm ≤ (n : ℝ) ^ 2 * S :=
    (linearPoly_coeffNorm_le_matOpNorm _).trans (mul_le_mul_of_nonneg_left hInvle (sq_nonneg _))
  have hForward : F.coeffNorm ≤ (1 + W) * S ^ Er := by
    calc
      _ ≤ S * (1 + W * S ^ (2 * E)) ^ 1 :=
        composition_bound_le (linearPoly J.linearPart) G (linearPoly_degree_le _) hLin hGn
      _ = S * (1 + W * S ^ (2 * E)) := by rw [pow_one]
      _ ≤ S * ((1 + W) * S ^ (2 * E)) :=
        mul_le_mul_of_nonneg_left (one_add_mul_pow_le hS (2 * E)) hSn
      _ = (1 + W) * S ^ (2 * E + 1) := by rw [pow_succ]; ring
      _ ≤ (1 + W) * S ^ Er := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hS (by dsimp [Er]; omega)) (by linarith)
  have hBackward : Finv.coeffNorm ≤ W * q ^ D * S ^ Er := by
    have hbase : 1 + (n : ℝ) ^ 2 * S ≤ q * S := by
      simpa only [pow_one] using (one_add_mul_pow_le (b := (n : ℝ) ^ 2) hS 1)
    calc
      _ ≤ (W * S ^ (2 * E)) * (1 + (n : ℝ) ^ 2 * S) ^ D :=
        composition_bound_le Ginv (linearPoly J.linearPart⁻¹) hdeginv hGinvn hLinInv
      _ ≤ (W * S ^ (2 * E)) * (q * S) ^ D := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hbase D) (by positivity)
      _ = W * q ^ D * S ^ Er := by dsimp [Er]; rw [mul_pow, pow_add]; ring
  have hraw : F.coeffNorm + Finv.coeffNorm ≤ Kr * S ^ Er := by
    calc
      _ ≤ (1 + W) * S ^ Er + W * q ^ D * S ^ Er := add_le_add hForward hBackward
      _ = _ := by dsimp [Kr]; ring
  have hpower : S ^ Er ≤ S ^ C := by
    calc
      S ^ Er = S ^ (Er : ℝ) := (Real.rpow_natCast S Er).symm
      _ ≤ S ^ C := Real.rpow_le_rpow_of_exponent_le hS hErC
  exact hraw.trans (mul_le_mul hKrC hpower (pow_nonneg hSn Er) (zero_le_one.trans hC))

end Yau.Proofs.Y02Aux
