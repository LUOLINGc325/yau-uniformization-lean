import Yau.Proofs.P06WeitzenbockTypeHodge

noncomputable section
open MeasureTheory
open scoped Matrix Manifold Topology ContDiff
namespace Yau.NodeProofs.P06Weitzenbock
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem realForm_neg_one_smul {k : ℕ} (F : RealForm M k) : (-1 : ℝ) • F = -F := by
  funext x
  apply ContinuousAlternatingMap.ext
  intro V
  change (-1 : ℝ) * (F x V) = -(F x V)
  ring

theorem projection_pythagoras (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    formNormSq h A x = formNormSq h (oneOneProjection A) x +
      formNormSq h (A - oneOneProjection A) x := by
  have ho := formInner_projection_residual h A x
  have hs := congrFun (L03.formInner_symm h (oneOneProjection A) (A - oneOneProjection A)) x
  have he : A = oneOneProjection A + (A - oneOneProjection A) := by abel
  change formInner h A A x = _
  calc
    _ = formInner h (oneOneProjection A + (A - oneOneProjection A))
        (oneOneProjection A + (A - oneOneProjection A)) x := by rw [← he]
    _ = _ := by
      simp only [L03.formInner_add_left, L03.formInner_add_right, Pi.add_apply]
      simp only [← hs, ho, add_zero, zero_add, formNormSq]

theorem projection_normSq_le (h : HermitianField M) (A : RealForm M 2) (x : M.Carrier) :
    formNormSq h (oneOneProjection A) x ≤ formNormSq h A x := by
  rw [projection_pythagoras h A x]
  exact le_add_of_nonneg_right (L03.formNormSq_nonneg h _ x)

theorem projection_hodge_residual_density (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (x : M.Carrier) :
    formInner g.form (L03.hodgeRealForm g.form 2 (A - oneOneProjection A))
        (A - oneOneProjection A) x =
      formInner g.form (L03.hodgeRealForm g.form 2 A) A x -
        formInner g.form (L03.hodgeRealForm g.form 2 (oneOneProjection A)) (oneOneProjection A) x := by
  have hp := oneOneProjection_smooth A hA
  have hh : L03.hodgeRealForm g.form 2 (A - oneOneProjection A) =
      L03.hodgeRealForm g.form 2 A - L03.hodgeRealForm g.form 2 (oneOneProjection A) := by
    have he := L03.hodgeRealForm_add g μ hμ A ((-1 : ℝ) • oneOneProjection A)
      hA (L03.smoothRealForm_smul _ _ hp)
    rw [L03.hodgeRealForm_smul g μ hμ (-1) _ hp] at he
    simpa only [realForm_neg_one_smul, sub_eq_add_neg] using he
  have hcomm := hodge_oneOneProjection g μ hμ hk A hA
  have hc₁ := formInner_oneOneProjection_selfadjoint g.form (L03.hodgeRealForm g.form 2 A)
    (oneOneProjection A) x
  rw [oneOneProjection_idempotent] at hc₁
  have hc₂ := formInner_oneOneProjection_selfadjoint g.form (L03.hodgeRealForm g.form 2 A) A x
  rw [hh, hcomm, L03.formInner_sub_left, L03.formInner_sub_right,
    L03.formInner_sub_right]
  simp only [Pi.sub_apply]
  rw [hc₁, hc₂]
  ring

theorem projection_hodge_energy_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    (∫ x, formInner g.form (L03.hodgeRealForm g.form 2 (oneOneProjection A))
      (oneOneProjection A) x ∂μ) ≤
    (∫ x, formInner g.form (L03.hodgeRealForm g.form 2 A) A x ∂μ) := by
  have hp := oneOneProjection_smooth A hA
  have hcp := oneOneProjection_compact A hcA
  have hsR : SmoothRealForm (A - oneOneProjection A) := by
    simpa only [realForm_neg_one_smul, sub_eq_add_neg] using
      (L03.smoothRealForm_add _ _ hA (L03.smoothRealForm_smul (-1) _ hp))
  have hcR : CompactlySupportedRealForm (A - oneOneProjection A) := by
    have hc : CompactlySupportedRealForm ((-1 : ℝ) • oneOneProjection A) :=
      L03.compactlySupportedRealForm_multiply (fun _ => (-1 : ℝ)) _ hcp
    simpa only [realForm_neg_one_smul, sub_eq_add_neg] using
      (L03.compactlySupportedRealForm_add A _ hcA hc)
  have hnonneg := L03.hodgeRealForm_nonnegative g μ hμ (A - oneOneProjection A) hsR hcR
  have hIA := L03.smooth_compact_formInner_integrable g μ hμ A (L03.hodgeRealForm g.form 2 A)
    hA (L03.hodgeRealForm_smooth g μ hμ A hA) hcA
  have hIP := L03.smooth_compact_formInner_integrable g μ hμ (oneOneProjection A)
    (L03.hodgeRealForm g.form 2 (oneOneProjection A)) hp
    (L03.hodgeRealForm_smooth g μ hμ _ hp) hcp
  rw [L03.formInner_symm g.form A _] at hIA
  rw [L03.formInner_symm g.form (oneOneProjection A) _] at hIP
  have he : (∫ x, formInner g.form (L03.hodgeRealForm g.form 2 (A - oneOneProjection A))
      (A - oneOneProjection A) x ∂μ) =
      (∫ x, formInner g.form (L03.hodgeRealForm g.form 2 A) A x ∂μ) -
      (∫ x, formInner g.form (L03.hodgeRealForm g.form 2 (oneOneProjection A))
        (oneOneProjection A) x ∂μ) := by
    rw [← integral_sub hIA hIP]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (projection_hodge_residual_density g μ hμ hk A hA))
  rw [he] at hnonneg
  linarith

theorem projection_q_le (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (A : RealForm M 2) (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    (∫ x, formNormSq g.form (L03.exteriorRealForm (oneOneProjection A)) x ∂μ) +
      (∫ x, formNormSq g.form (L03.codifferentialRealForm g.form (oneOneProjection A)) x ∂μ) ≤
    (∫ x, formNormSq g.form (L03.exteriorRealForm A) x ∂μ) +
      (∫ x, formNormSq g.form (L03.codifferentialRealForm g.form A) x ∂μ) := by
  have he := projection_hodge_energy_le g μ hμ hk A hA hcA
  rw [L03.integral_hodgeRealForm_succ_energy g μ hμ _ _
    (oneOneProjection_smooth A hA) (oneOneProjection_smooth A hA)
    (oneOneProjection_compact A hcA) (oneOneProjection_compact A hcA),
    L03.integral_hodgeRealForm_succ_energy g μ hμ A A hA hA hcA hcA] at he
  simpa only [formNormSq, add_comm] using he

end Yau.NodeProofs.P06Weitzenbock
