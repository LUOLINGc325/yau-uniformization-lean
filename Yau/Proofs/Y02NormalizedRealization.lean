import Yau.Proofs.Y02StageShearBounds
import Yau.Proofs.Y02JacobianDiscrepancy

/-! Uniform finite-jet realization with explicit bounds chosen before the input. -/

noncomputable section

open scoped BigOperators

namespace Yau.Proofs.Y02Aux

theorem normalized_volume_realization_succ (n d : ℕ) :
    ∃ (D : ℕ) (K : ℝ) (E : ℕ), 1 ≤ D ∧ 1 ≤ K ∧ 1 ≤ E ∧
      ∀ P : PolyMap n, tangentId P → positiveJacFlat P (d + 1) →
        ∃ G Ginv : PolyMap n, IsPolyAutomorphism G Ginv ∧
          tangentId G ∧ tangentId Ginv ∧ G.jacDet = 1 ∧ Ginv.jacDet = 1 ∧
          PolyMap.JetEq G P (d + 1) ∧ G.degree ≤ D ∧ Ginv.degree ≤ D ∧
          G.coeffNorm + Ginv.coeffNorm ≤ K * (1 + P.coeffNorm) ^ E := by
  induction d with
  | zero =>
    refine ⟨1, 2 * (n : ℝ) + 1, 1, le_rfl, ?_, le_rfl, ?_⟩
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    · intro P hP hflat
      refine ⟨PolyMap.id, PolyMap.id, automorphism_id, tangentId_id, tangentId_id,
        jacDet_id, jacDet_id, ?_, degree_id_le_one, degree_id_le_one, ?_⟩
      · exact jetEq_symm ((tangentId_iff_jetEq P).mp hP)
      · rw [coeffNorm_id, pow_one]
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [coeffNorm_nonneg P]
  | succ d ih =>
    obtain ⟨D, K, E, hD, hK, hE, hOld⟩ := ih
    let m := d + 2
    have hm : 2 ≤ m := by omega
    obtain ⟨N, l, v, R, Cm, hCm, horth, hsynth, hRbound⟩ := exists_fixed_shear_decomposition n m hm
    let L := List.finRange N
    let B : ℝ := ∑ i, (shearField (l i) (v i) m).coeffNorm
    let a : ℝ := (n : ℝ) + 1 + B * Cm * (1 + K)
    have hB : 0 ≤ B := Finset.sum_nonneg fun i hi => coeffNorm_nonneg _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have ha : 1 ≤ a := by
      have hz : 0 ≤ B * Cm * (1 + K) := mul_nonneg (mul_nonneg hB hCm) (by linarith)
      dsimp [a]
      linarith
    let b := shearBounds m E a L (D, K, E)
    obtain ⟨hDnew, hKnew, hEnew⟩ :=
      shearBounds_lower m E a L (D, K, E) (by omega) hE ha hD hK hE
    refine ⟨b.1, b.2.1, b.2.2, hDnew, hKnew, hEnew, ?_⟩
    intro P hP hflat
    obtain ⟨G₀, G₀inv, hpair, hG₀, hG₀inv, hdet, hdetinv, hjet, hdeg, hdeginv, hnorm⟩ :=
      hOld P hP (positiveJacFlat_mono hflat (by omega))
    have hjet' : PolyMap.JetEq P G₀ (m - 1) := by
      have hpred : m - 1 = d + 1 := by omega
      rw [hpred]
      exact jetEq_symm hjet
    let H := firstDiscrepancy m P G₀
    have hH : H ∈ homogeneousFields n m := homogeneousPart_mem m (P - G₀)
    have hdiv : divergence n H = 0 := firstDiscrepancy_divergence_zero hm le_rfl P G₀ hP hG₀
      hjet' hflat (positiveJacFlat_of_jacDet_one G₀ hdet m)
    let X : DivFreeHom n m := ⟨H, hH, hdiv⟩
    let c : Fin N → ℂ := R H
    let t : ℝ := 1 + P.coeffNorm
    have ht : 1 ≤ t := by dsimp [t]; linarith [coeffNorm_nonneg P]
    have hHnorm : H.coeffNorm ≤ (1 + K) * t ^ E :=
      firstDiscrepancy_stage_bound m E hE K P G₀ G₀inv hnorm
    have hc : (∑ i, ‖c i‖) ≤ Cm * (1 + K) * t ^ E := by
      apply (hRbound H hH).trans
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hHnorm hCm
    have hparameters := stage_shear_bounds l v m E c Cm K t hCm (zero_le_one.trans hK) ht hc
    have hS : ∀ i, (shear (l i) (v i) m (c i)).coeffNorm ≤ a * t ^ E :=
      fun i => (hparameters.2 i).1
    have hT : ∀ i, (shear (l i) (v i) m (-c i)).coeffNorm ≤ a * t ^ E :=
      fun i => (hparameters.2 i).2
    have hbounds := shearFold_bound l v hm c L E a t ht (zero_le_one.trans ha) hS hT
      (D, K, E) (zero_le_one.trans hK) G₀ G₀inv hdeg hdeginv hnorm
    obtain ⟨hpairF, hGF, hGinvF, hdetF, hdetinvF, hjetF⟩ :=
      shearFold_properties l v hm c horth L G₀ G₀inv hpair hG₀ hG₀inv hdet hdetinv
    have hsum : (L.map (fun i => c i • shearField (l i) (v i) m)).sum = H := by
      rw [show L = List.finRange N from rfl, ← List.ofFn_eq_map, List.sum_ofFn]
      exact hsynth X
    rw [hsum] at hjetF
    have hcorrect : PolyMap.JetEq (G₀ + H) P m := firstDiscrepancy_corrects (by omega) hjet'
    refine ⟨shearFoldForward l v m c L G₀, shearFoldInverse l v m c L G₀inv,
      hpairF, hGF, hGinvF, hdetF, hdetinvF, ?_, hbounds.1, hbounds.2.1, hbounds.2.2⟩
    exact jetEq_trans hjetF hcorrect

theorem normalized_volume_realization (n d : ℕ) (hd : 1 ≤ d) :
    ∃ (D : ℕ) (K : ℝ) (E : ℕ), 1 ≤ D ∧ 1 ≤ K ∧ 1 ≤ E ∧
      ∀ P : PolyMap n, tangentId P → positiveJacFlat P d →
        ∃ G Ginv : PolyMap n, IsPolyAutomorphism G Ginv ∧
          tangentId G ∧ tangentId Ginv ∧ G.jacDet = 1 ∧ Ginv.jacDet = 1 ∧
          PolyMap.JetEq G P d ∧ G.degree ≤ D ∧ Ginv.degree ≤ D ∧
          G.coeffNorm + Ginv.coeffNorm ≤ K * (1 + P.coeffNorm) ^ E := by
  have h := normalized_volume_realization_succ n (d - 1)
  simpa only [Nat.sub_add_cancel hd] using h

end Yau.Proofs.Y02Aux
