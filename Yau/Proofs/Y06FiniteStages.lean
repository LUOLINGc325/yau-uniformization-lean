import Yau.Proofs.Y06SupportAlgebra
import Yau.Proofs.Y06LayerIdentity

/-! Finite masks admit complete homological jet identities, constructed
one homogeneous degree at a time by the actual backward recursion. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Proofs.Y06Aux

open MvPolynomial Yau.Blueprint Yau.Blueprint.Alignment Yau.Proofs.Y02Aux
open Yau.Proofs.Y01Aux

variable {n : ℕ}

theorem linearPolynomial_as_linearPoly (A : Herm n) : linearPolynomial A = linearPoly A := rfl

def layerRight (P H : ℕ → PolyMap n) (J : ℕ → Herm n) (k : ℕ) : PolyMap n :=
  (linearPolynomial (J k)⁻¹).comp ((H (k + 1)).comp ((linearPolynomial (J k)).comp (P k)))

def stageDiscrepancy (m : ℕ) (P H G : ℕ → PolyMap n) (J : ℕ → Herm n) (k : ℕ) : PolyMap n :=
  homogeneousPart m (layerRight P H J k - (G k).comp (H k))

def finiteJetStage (b : ℕ) (active : ℕ → Prop) (D J : ℕ → Herm n)
    (w : ℕ → Fin n → ℝ) (P : ℕ → PolyMap n) : ℕ → (ℕ → PolyMap n) × (ℕ → PolyMap n)
  | 0 => (fun _ => PolyMap.id, fun k => if active k then linearPolynomial (D k) else PolyMap.id)
  | r + 1 =>
    let old := finiteJetStage b active D J w P r
    let B := stageDiscrepancy (r + 2) P old.1 old.2 J
    let u := finiteLayerCorrection b active D J w B
    let v := finiteLayerModel b active D J w B
    (fun k => old.1 k + u k, fun k => old.2 k + v k)

def FiniteStageSpec (active : ℕ → Prop) (D J : ℕ → Herm n)
    (w : ℕ → Fin n → ℝ) (P H G : ℕ → PolyMap n) (m : ℕ) : Prop :=
  (∀ k, ¬active k → H k = PolyMap.id ∧ G k = PolyMap.id) ∧
  (∀ k, tangentId (H k) ∧ (H k).degree ≤ m ∧ OnlyForbidden (H k) (w k)) ∧
  ∀ k, active k → (G k).FixesZero ∧ (G k).linearPart = D k ∧
    (G k).degree ≤ m ∧ Allowed (G k) (w k) ∧
    PolyMap.JetEq ((G k).comp (H k)) (layerRight P H J k) m

theorem stageDiscrepancy_homogeneous (m : ℕ) (P H G : ℕ → PolyMap n)
    (J : ℕ → Herm n) (k : ℕ) : Homogeneous (stageDiscrepancy m P H G J k) m :=
  (homogeneous_iff_components _).mpr (homogeneousPart_mem _ _)

theorem finiteJetStage_spec (b : ℕ) (active : ℕ → Prop)
    (a : ℕ → Fin n → ℂ) (ha : ∀ k i, a k i ≠ 0) (J : ℕ → Herm n)
    (hJ : ∀ k, active k → IsUnit (J k)) (w : ℕ → Fin n → ℝ) (P : ℕ → PolyMap n)
    (hP0 : ∀ k, (P k).FixesZero) (hPD : ∀ k, (P k).linearPart = Matrix.diagonal (a k))
    (hactive : ∀ k, active k → k < b) (r : ℕ) :
    let D := fun k => Matrix.diagonal (a k)
    let Q := finiteJetStage b active D J w P r
    FiniteStageSpec active D J w P Q.1 Q.2 (r + 1) := by
  let D := fun k => Matrix.diagonal (a k)
  change FiniteStageSpec active D J w P
    (finiteJetStage b active D J w P r).1 (finiteJetStage b active D J w P r).2 (r + 1)
  induction r with
  | zero =>
    change FiniteStageSpec active D J w P (fun _ => PolyMap.id)
      (fun k => if active k then linearPolynomial (D k) else PolyMap.id) 1
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      exact ⟨rfl, by simp only [ite_eq_right hk]⟩
    · intro k
      refine ⟨tangentId_id, ?_, onlyForbidden_id (w k)⟩
      change (PolyMap.id : PolyMap n).degree ≤ 1
      rw [← linearPoly_one]
      exact linearPoly_degree_le 1
    · intro k hk
      dsimp only
      simp only [ite_eq_left hk]
      refine ⟨linearPoly_fixesZero _, linearPoly_linearPart _, linearPoly_degree_le _,
        allowed_linearPolynomial _ _, ?_⟩
      have hPJ : ((linearPolynomial (J k)).comp (P k)).FixesZero :=
        comp_fixesZero (linearPoly_fixesZero _) (hP0 k)
      have hR0 : ((linearPolynomial (J k)⁻¹).comp ((linearPolynomial (J k)).comp (P k))).FixesZero :=
        comp_fixesZero (linearPoly_fixesZero _) hPJ
      have hRlin : ((linearPolynomial (J k)⁻¹).comp ((linearPolynomial (J k)).comp (P k))).linearPart = D k := by
        change ((linearPoly (J k)⁻¹).comp ((linearPoly (J k)).comp (P k))).linearPart = D k
        rw [linearPoly_comp_linearPart, linearPoly_comp_linearPart, hPD k, ← Matrix.mul_assoc]
        rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (hJ k hk)), Matrix.one_mul]
      have h := jetEq_linear_of_fixesZero hR0
      rw [hRlin] at h
      simpa only [finiteJetStage, layerRight, comp_id, id_comp, linearPolynomial_as_linearPoly] using jetEq_symm h
  | succ r ih =>
    let old := finiteJetStage b active D J w P r
    let B := stageDiscrepancy (r + 2) P old.1 old.2 J
    let u := finiteLayerCorrection b active D J w B
    let v := finiteLayerModel b active D J w B
    change FiniteStageSpec active D J w P old.1 old.2 (r + 1) at ih
    have hB : ∀ k, Homogeneous (B k) (r + 2) := stageDiscrepancy_homogeneous _ _ _ _ _
    have hu : ∀ k, Homogeneous (u k) (r + 2) := finiteLayerCorrection_homogeneous b active D J w B hB
    have hv : ∀ k, Homogeneous (v k) (r + 2) := finiteLayerModel_homogeneous b active D J w B hB
    change FiniteStageSpec active D J w P (fun k => old.1 k + u k) (fun k => old.2 k + v k) (r + 1 + 1)
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have hu0 : u k = 0 := finiteLayerCorrection_inactive b active D J w B hk
      have hv0 : v k = 0 := by simp only [v, finiteLayerModel, ite_eq_right hk]
      exact ⟨by change old.1 k + u k = _; rw [(ih.1 k hk).1, hu0, add_zero],
        by change old.2 k + v k = _; rw [(ih.1 k hk).2, hv0, add_zero]⟩
    · intro k
      refine ⟨tangentId_add_homogeneous (ih.2.1 k).1 (hu k) (by omega), ?_, ?_⟩
      · exact (polynomial_degree_add_le _ _).trans
          (max_le ((ih.2.1 k).2.1.trans (by omega)) (homogeneous_degree_le (hu k)))
      · exact onlyForbidden_add (ih.2.1 k).2.2 (finiteLayerCorrection_forbidden b active D J w B k)
    · intro k hk
      obtain ⟨hG0, hGlin, hGdeg, hGall, hGold⟩ := ih.2.2 k hk
      refine ⟨polynomial_fixesZero_add hG0 (homogeneous_fixesZero (hv k) (by omega)), ?_, ?_, ?_, ?_⟩
      · rw [polynomial_linearPart_add, hGlin, homogeneous_linearPart_zero (hv k) (by omega), add_zero]
      · exact (polynomial_degree_add_le _ _).trans
          (max_le (hGdeg.trans (by omega)) (homogeneous_degree_le (hv k)))
      · exact allowed_add hGall (finiteLayerModel_allowed b active D J w B k)
      · apply complete_layer_identity (P k) (old.1 k) (old.1 (k + 1)) (old.2 k)
          (u k) (u (k + 1)) (v k) (D k) (J k) (by omega) (hP0 k) (hPD k)
          hG0 hGlin (ih.2.1 k).1 (hu k) (hu (k + 1)) (hv k)
        · simpa only [layerRight, show r + 2 - 1 = r + 1 by omega] using hGold
        · exact finiteLayer_equation b active a ha J w B (hactive k hk) hk

end Yau.Proofs.Y06Aux
