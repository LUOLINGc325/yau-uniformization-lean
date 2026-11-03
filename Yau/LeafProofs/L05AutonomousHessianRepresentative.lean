import Yau.LeafProofs.L05AutonomousContinuousRepresentative
import Yau.LeafProofs.L05AutonomousHessianRepresentativeNorms
import Yau.LeafProofs.L05AutonomousHessianRepresentativeMeasurable

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

local instance autoHessianRepresentativeMatGroup (n : ℕ) : NormedAddCommGroup (Mat n) :=
  Matrix.frobeniusNormedAddCommGroup
local instance autoHessianRepresentativeMatSpace (n : ℕ) : NormedSpace ℝ (Mat n) :=
  Matrix.frobeniusNormedSpace

/-- Finite directional bounds give a continuous symmetric matrix representative
and a genuinely measurable, globally bounded bilinear field. -/
theorem auto_hessian_representative (n N : ℕ) (e : Fin N → Space n)
    (hRecon : ∀ H : Sym n,
      ‖(H : Mat n)‖ ≤ (2*n : ℝ)*2*∑ j, |autoBilinearMap n H (e j) (e j)|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ eta B K : ℝ, 0 < eta → 0 ≤ B → 0 ≤ K →
      ∀ H : Point n → Sym n, ∀ S : Set (Point n),
        S ⊆ autoOpen (0 : Space n) (9/16) 0 →
        (∀ᵐ p ∂volume.restrict (autoOpen (0 : Space n) (9/16) 0), p ∈ S) →
        (∀ p ∈ S, ‖(H p : Mat n)‖ ≤ B) →
        (∀ j, ∀ p ∈ S, ∀ q ∈ S,
          |autoBilinearMap n (H p) (e j) (e j)-autoBilinearMap n (H q) (e j) (e j)| ≤
            K*holderWeight eta p q) →
      ∃ Hbar : Point n → Sym n,
      ∃ HB : Point n → (Space n →L[ℝ] Space n →L[ℝ] ℝ),
        ContinuousOn Hbar (autoClosed (0 : Space n) (9/16) 0) ∧ EqOn Hbar H S ∧
        (∀ p ∈ autoClosed (0 : Space n) (9/16) 0, ‖(Hbar p : Mat n)‖ ≤ C*B) ∧
        (∀ p ∈ autoClosed (0 : Space n) (9/16) 0,
          ∀ q ∈ autoClosed (0 : Space n) (9/16) 0,
          ‖(Hbar p : Mat n)-(Hbar q : Mat n)‖ ≤ C*K*holderWeight eta p q) ∧
        StronglyMeasurable HB ∧ ContinuousOn HB (autoClosed (0 : Space n) (9/16) 0) ∧
        (∀ p, ∀ v z, HB p v z=HB p z v) ∧
        (∀ p ∈ autoClosed (0 : Space n) (9/16) 0, HB p=autoBilinearMap n (Hbar p)) ∧
        (∀ p, ‖HB p‖ ≤ C*B) ∧
        (∀ p ∈ autoClosed (0 : Space n) (9/16) 0,
          ∀ q ∈ autoClosed (0 : Space n) (9/16) 0,
          ‖HB p-HB q‖ ≤ C*K*holderWeight eta p q) := by
  classical
  let L : ℝ := (2*n : ℝ)*2*(N : ℝ)
  let D : ℝ := spatialGradientDimensionBudget n
  let C : ℝ := 1+L+D+D*L
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hD : 0 < D := spatialGradientDimensionBudget_pos n
  have hDL : 0 ≤ D*L := mul_nonneg hD.le hL
  have hC : 0 < C := by dsimp [C]; positivity
  have hOneC : 1 ≤ C := by dsimp [C]; linarith only [hL,hD,hDL]
  have hLC : L ≤ C := by dsimp [C]; linarith only [hD,hDL]
  have hDC : D ≤ C := by dsimp [C]; linarith only [hL,hDL]
  have hDLC : D*L ≤ C := by dsimp [C]; linarith only [hL,hD]
  refine ⟨C,hC,?_⟩
  intro eta B K heta hB hK H S hS hFull hBound hDir
  let Q : Set (Point n) := autoClosed (0 : Space n) (9/16) 0
  have hPair : ∀ p ∈ S, ∀ q ∈ S,
      ‖(H p : Mat n)-(H q : Mat n)‖ ≤ (L*K)*holderWeight eta p q :=
    auto_hessian_frobenius_pair e hRecon hDir
  obtain ⟨A,hA,hAEq,hABound,hAPair⟩ :=
    auto_full_measure_cylinder_holder_representative (E := Mat n) (0 : Space n)
      (by norm_num : (0 : ℝ)<9/16) hS hFull heta (mul_nonneg hL hK) hB
      (fun p => (H p : Mat n)) hBound hPair
  let Hbar : Point n → Sym n := fun p => sym (A p)
  have hHbar : ContinuousOn Hbar Q :=
    (continuous_selfAdjointPart ℝ (Mat n)).comp_continuousOn hA
  have hHEq : EqOn Hbar H S := by
    intro p hp
    change sym (A p)=H p
    rw [hAEq hp]
    exact (H p).property.selfAdjointPart_apply ℝ
  have hHBound : ∀ p ∈ Q, ‖(Hbar p : Mat n)‖ ≤ B := by
    intro p hp
    exact (auto_hessian_sym_frobenius_norm_le (A p)).trans (hABound p hp)
  have hHPair : ∀ p ∈ Q, ∀ q ∈ Q,
      ‖(Hbar p : Mat n)-(Hbar q : Mat n)‖ ≤ (L*K)*holderWeight eta p q := by
    intro p hp q hq
    exact (auto_hessian_sym_frobenius_sub_le (A p) (A q)).trans (hAPair p hp q hq)
  let F : Point n → (Space n →L[ℝ] Space n →L[ℝ] ℝ) := fun p => autoBilinearMap n (Hbar p)
  have hF : ContinuousOn F Q := (autoBilinearMap n).continuous.comp_continuousOn hHbar
  have hQ : IsClosed Q := Metric.isClosed_closedBall.prod isClosed_Icc
  let HB : Point n → (Space n →L[ℝ] Space n →L[ℝ] ℝ) := Q.piecewise F (fun _ => 0)
  have hHBEq : ∀ p ∈ Q, HB p=autoBilinearMap n (Hbar p) := by
    intro p hp
    simp only [HB,Set.piecewise,if_pos hp,F]
  have hSM : StronglyMeasurable HB := by
    change StronglyMeasurable (Q.piecewise F (fun _ => 0))
    exact auto_hessian_piecewise_stronglyMeasurable
      (n := n) (E := Space n →L[ℝ] Space n →L[ℝ] ℝ) (Q := Q) (f := F) hQ.measurableSet hF
  have hHB : ContinuousOn HB Q := by
    change ContinuousOn (Q.piecewise F (fun _ => 0)) Q
    exact auto_hessian_piecewise_continuousOn
      (n := n) (E := Space n →L[ℝ] Space n →L[ℝ] ℝ) (Q := Q) (f := F) hF
  have hWeight (p q : Point n) : 0 ≤ holderWeight eta p q := by
    unfold holderWeight
    positivity
  refine ⟨Hbar,HB,hHbar,hHEq,?_,?_,hSM,hHB,?_,hHBEq,?_,?_⟩
  · intro p hp
    exact (hHBound p hp).trans (by nlinarith only [mul_nonneg (sub_nonneg.mpr hOneC) hB])
  · intro p hp q hq
    have h := mul_le_mul_of_nonneg_right hLC (mul_nonneg hK (hWeight p q))
    exact (hHPair p hp q hq).trans (by nlinarith only [h])
  · intro p v z
    by_cases hp : p ∈ Q
    · rw [hHBEq p hp]
      exact autoBilinearMap_symmetric (Hbar p) v z
    · simp [HB,Set.piecewise,hp]
  · intro p
    by_cases hp : p ∈ Q
    · rw [hHBEq p hp]
      have h := auto_hessian_bilinear_frobenius_bound (Hbar p)
      exact h.trans ((mul_le_mul_of_nonneg_left (hHBound p hp) hD.le).trans
        (mul_le_mul_of_nonneg_right hDC hB))
    · have hOff : HB p=(0 : Space n →L[ℝ] Space n →L[ℝ] ℝ) := by
        simp only [HB,Set.piecewise,if_neg hp]
      rw [hOff]
      rw [ContinuousLinearMap.opNorm_zero]
      exact mul_nonneg hC.le hB
  · intro p hp q hq
    rw [hHBEq p hp,hHBEq q hq]
    have h := auto_hessian_bilinear_sub_frobenius_bound (Hbar p) (Hbar q)
    apply h.trans
    have h1 := mul_le_mul_of_nonneg_left (hHPair p hp q hq) hD.le
    have h2 := mul_le_mul_of_nonneg_right hDLC (mul_nonneg hK (hWeight p q))
    nlinarith only [h1,h2]

end Yau.LeafProofs.L05AutonomousAux
