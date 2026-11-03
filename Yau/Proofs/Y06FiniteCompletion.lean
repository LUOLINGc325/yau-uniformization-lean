import Yau.Proofs.Y06FiniteVolume
import Yau.Proofs.Y06InverseEnvelopes
import Yau.Proofs.Y06RegularLimit
import Yau.Proofs.Y06UniformFinite

/-! Complete the finite correction/model pair by actual inverse jets and
true polynomial model inverses, with constants independent of the horizon. -/

noncomputable section

namespace Yau.Proofs.Y06Aux

open Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux Yau.Proofs.Y01Aux

variable {n d : ℕ}

def inverseJetEnvelopeExponent (C E : ℝ) : ℝ := |C| + |C| * (E + 1)

def inverseModelEnvelopeExponent (n d : ℕ) (E A : ℝ) : ℝ :=
  (triangularInverseExponent d n : ℝ) * ((n + 2 : ℝ) + 2 * E + A)

def completionConstant (n d : ℕ) (C E A : ℝ) : ℝ :=
  (n + 4 : ℝ) + 2 * E + inverseJetEnvelopeExponent C E + inverseModelEnvelopeExponent n d E A

theorem four_exp_sum_bound {a b c e A B C D x : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hx : 1 ≤ x)
    (ha : a ≤ Real.exp (A * x)) (hb : b ≤ Real.exp (B * x))
    (hc : c ≤ Real.exp (C * x)) (he : e ≤ Real.exp (D * x)) :
    a + b + c + e ≤ Real.exp ((A + B + C + D + 4) * x) := by
  let S := A + B + C + D
  have hx0 : 0 ≤ x := by linarith
  have h₁ := ha.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [S]; linarith : A ≤ S) hx0))
  have h₂ := hb.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [S]; linarith : B ≤ S) hx0))
  have h₃ := hc.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [S]; linarith : C ≤ S) hx0))
  have h₄ := he.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by dsimp [S]; linarith : D ≤ S) hx0))
  have h4 : (4 : ℝ) ≤ Real.exp (4 * x) := by have := Real.add_one_le_exp (4 * x); linarith
  calc
    _ ≤ 4 * Real.exp (S * x) := by linarith
    _ ≤ Real.exp (4 * x) * Real.exp (S * x) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; dsimp [S]; congr 1; ring

theorem complete_finite_stage {Dd : ℕ} {C E A : ℝ}
    (hrealize : ∀ P : PolyMap n, IsConstantVolumeJet P d →
      ∃ R S : PolyMap n, IsPolyAutomorphism R S ∧ PolyMap.JetEq R P d ∧
        R.degree ≤ Dd ∧ S.degree ≤ Dd ∧
        R.coeffNorm + S.coeffNorm ≤ C * (1 + P.coeffNorm + matOpNorm P.linearPart⁻¹) ^ C)
    (hd : 1 ≤ d) (hE : 0 ≤ E) (hA : 0 ≤ A) (s : ℕ → ℝ) (hs : ∀ k, 1 ≤ s k)
    (active : ℕ → Prop) (a : ℕ → Fin n → ℂ) (ha : ∀ k i, a k i ≠ 0)
    (J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (P H G : ℕ → PolyMap n)
    (hSpec : FiniteStageSpec active (fun k => Matrix.diagonal (a k)) J w P H G d)
    (hCV : ∀ k, IsConstantVolumeJet (H k) d)
    (hw : ∀ k, active k → ∀ i, 1 ≤ w k i)
    (hsize : ∀ k, polySize (H k) ≤ Real.exp (E * Real.sqrt (s k)) ∧
      polySize (G k) ≤ Real.exp (E * Real.sqrt (s k)))
    (hDi : ∀ k, active k → polySize (linearPolynomial (Matrix.diagonal (a k))⁻¹) ≤
      Real.exp (A * Real.sqrt (s k))) :
    ∃ Q : JetData n,
      RegularJetSolution (fun k => (P k).eval) (fun k => Matrix.diagonal (a k)) J w active
        d (d ^ (n + 1)) s (completionConstant n d C E A) Q ∧
      Q.correction = H ∧ Q.model = G ∧ JetDataDegreeBound (d ^ (n + 1)) Q ∧
      JetDataNormBound (fun k => Real.exp (completionConstant n d C E A * Real.sqrt (s k))) Q := by
  classical
  let I₀ := fun k => Classical.choose (inverseJet_of_volumeJets hrealize (H k) (hCV k))
  have hI₀ k := Classical.choose_spec (inverseJet_of_volumeJets hrealize (H k) (hCV k))
  let I := fun k => if active k then I₀ k else PolyMap.id
  let GI := fun k => if active k then triangularInverseApprox (G k) (a k) n else PolyMap.id
  let Q : JetData n := ⟨H, I, G, GI⟩
  let CI := inverseJetEnvelopeExponent C E
  let CG := inverseModelEnvelopeExponent n d E A
  let Ctotal := completionConstant n d C E A
  have hCI : 0 ≤ CI := by dsimp [CI, inverseJetEnvelopeExponent]; positivity
  have hCG : 0 ≤ CG := by dsimp [CG, inverseModelEnvelopeExponent]; positivity
  have hCtotal : (n + 1 : ℝ) ≤ Ctotal := by dsimp [Ctotal, completionConstant]; linarith
  have hEtotal : E ≤ Ctotal := by dsimp [Ctotal, completionConstant] at *; linarith
  have hItotal : CI ≤ Ctotal := by dsimp [Ctotal, completionConstant] at *; linarith
  have hGtotal : CG ≤ Ctotal := by dsimp [Ctotal, completionConstant] at *; linarith
  have hNormMono {x B : ℝ} (hx : 0 ≤ x) (hB : B ≤ Ctotal) : Real.exp (B * x) ≤ Real.exp (Ctotal * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hB hx)
  have hInactive k (hk : ¬active k) : Q.correction k = PolyMap.id ∧ Q.inverseJet k = PolyMap.id ∧
      Q.model k = PolyMap.id ∧ Q.inverseModel k = PolyMap.id := by
    exact ⟨(hSpec.1 k hk).1, by dsimp [Q, I]; exact ite_eq_right hk,
      (hSpec.1 k hk).2, by dsimp [Q, GI]; exact ite_eq_right hk⟩
  have hIb k (hk : active k) : (I k).coeffNorm ≤ Real.exp (CI * Real.sqrt (s k)) := by
    rw [show I k = I₀ k from ite_eq_left hk]
    exact realization_inverse_envelope hE (sqrt_one_le (hs k)) (hSpec.2.1 k).1.2 (hsize k).1 (hI₀ k).2.2.2.2
  have hGIb k (hk : active k) : (GI k).coeffNorm ≤ Real.exp (CG * Real.sqrt (s k)) := by
    rw [show GI k = triangularInverseApprox (G k) (a k) n from ite_eq_left hk]
    have hD := hDi k hk
    rw [diagonal_inverse_eq (a k) (ha k)] at hD
    exact triangular_inverse_envelope (G k) (a k) hd (hSpec.2.2 k hk).2.2.1
      (sqrt_one_le (hs k)) (hsize k).2 hD
  have hHb k : (H k).coeffNorm ≤ Real.exp (E * Real.sqrt (s k)) := by
    have := (hsize k).1; dsimp [polySize] at this; linarith
  have hGb k : (G k).coeffNorm ≤ Real.exp (E * Real.sqrt (s k)) := by
    have := (hsize k).2; dsimp [polySize] at this; linarith
  have hdD : d ≤ d ^ (n + 1) := by
    have h := Nat.mul_le_mul_right d (one_le_pow₀ hd (n := n))
    simpa only [pow_succ, one_mul] using h
  have hID : (PolyMap.id : PolyMap n).degree ≤ d ^ (n + 1) := by
    have h := (constantVolume_id hd : IsConstantVolumeJet (PolyMap.id : PolyMap n) d).2.1
    exact h.trans hdD
  refine ⟨Q, ?_, rfl, rfl, ?_, ?_⟩
  · refine ⟨fun k hk => ⟨(hInactive k hk).1, (hInactive k hk).2.1⟩, ?_⟩
    intro k hk
    obtain ⟨hG0, hGlin, hGdeg, hGall, hGjet⟩ := hSpec.2.2 k hk
    obtain ⟨hAuto, hGIdeg, hJac⟩ := finiteStage_model_data ha hSpec hw hd k hk
    have hIk : I k = I₀ k := ite_eq_left hk
    have hGIk : GI k = triangularInverseApprox (G k) (a k) n := ite_eq_left hk
    refine ⟨(hSpec.2.1 k).1.2, (hSpec.2.1 k).2.1, hCV k, ?_, ?_, ?_, ?_,
      (hSpec.2.1 k).2.2, hG0, hGlin, hGall, ?_, hGdeg.trans hdD, ?_, hJac, ?_, ?_⟩
    · change (I k).degree ≤ d; rw [hIk]; exact (hI₀ k).1
    · change (I k).FixesZero; rw [hIk]; exact (hI₀ k).2.1
    · change PolyMap.JetEq ((H k).comp (I k)) PolyMap.id d; rw [hIk]; exact (hI₀ k).2.2.1
    · change PolyMap.JetEq ((I k).comp (H k)) PolyMap.id d; rw [hIk]; exact (hI₀ k).2.2.2.1
    · change IsPolyAutomorphism (G k) (GI k); rw [hGIk]; exact hAuto
    · change (GI k).degree ≤ d ^ (n + 1); rw [hGIk]
      exact hGIdeg.trans (pow_le_pow_right₀ hd (Nat.le_succ n))
    · exact germJetEq_transport (funext (polyMap_eval_comp _ _))
        (layerRight_eval_fun P H J k) (jetEq_germJetEq hGjet)
    · have hsum := four_exp_sum_bound hE hCI hE hCG (sqrt_one_le (hs k)) (hHb k) (hIb k hk) (hGb k) (hGIb k hk)
      exact hsum.trans (hNormMono (Real.sqrt_nonneg _) (by dsimp [Ctotal, completionConstant, CI, CG]; have := Nat.cast_nonneg (α := ℝ) n; linarith))
  · intro k
    by_cases hk : active k
    · have hIk : I k = I₀ k := ite_eq_left hk
      have hGIk : GI k = triangularInverseApprox (G k) (a k) n := ite_eq_left hk
      refine ⟨(hSpec.2.1 k).2.1.trans hdD, ?_, (hSpec.2.2 k hk).2.2.1.trans hdD, ?_⟩
      · change (I k).degree ≤ _; rw [hIk]; exact (hI₀ k).1.trans hdD
      · change (GI k).degree ≤ _; rw [hGIk]
        exact ((finiteStage_model_data ha hSpec hw hd k hk).2.1).trans (pow_le_pow_right₀ hd (Nat.le_succ n))
    · obtain ⟨hHid, hIid, hGid, hGIid⟩ := hInactive k hk
      rw [hHid, hIid, hGid, hGIid]
      exact ⟨hID, hID, hID, hID⟩
  · intro k
    by_cases hk : active k
    · exact ⟨(hHb k).trans (hNormMono (Real.sqrt_nonneg _) hEtotal),
        (hIb k hk).trans (hNormMono (Real.sqrt_nonneg _) hItotal),
        (hGb k).trans (hNormMono (Real.sqrt_nonneg _) hEtotal),
        (hGIb k hk).trans (hNormMono (Real.sqrt_nonneg _) hGtotal)⟩
    · obtain ⟨hHid, hIid, hGid, hGIid⟩ := hInactive k hk
      rw [hHid, hIid, hGid, hGIid]
      have hIdb := polySize_id_exp hCtotal (sqrt_one_le (hs k))
      have hId : (PolyMap.id : PolyMap n).coeffNorm ≤ Real.exp (Ctotal * Real.sqrt (s k)) := by dsimp [polySize] at hIdb; linarith
      exact ⟨hId, hId, hId, hId⟩

end Yau.Proofs.Y06Aux
