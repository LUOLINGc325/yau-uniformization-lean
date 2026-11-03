import Yau.Proofs.P06ExteriorHodge

noncomputable section
open MeasureTheory
open scoped Topology

namespace Yau.NodeProofs.P06Aux
open Yau Yau.LeafProofs.L03
variable {n k : ℕ} {M : ComplexManifold n}

/-- Genuine compact smooth form tests separate arbitrary smooth forms;
global L² integrability of the form being tested is not needed. -/
theorem smoothForm_zero_of_compact_pairings (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (W : RealForm M k) (hW : SmoothRealForm W)
    (hpair : ∀ B : RealForm M k, SmoothRealForm B → CompactlySupportedRealForm B →
      (∫ y, formInner g.form W B y ∂μ) = 0) : W = 0 := by
  funext x
  obtain ⟨η, hη, hcη, _, hηone, _⟩ := Yau.LeafProofs.L18Aux.exists_smooth_compact_cutoff g x
    (r := 1) (R := 2) (by norm_num) (by norm_num)
  have hV := smoothRealForm_multiply η W hη hW
  have hcV := compactlySupportedRealForm_multiply_scalar η hcη W
  have hVL := smooth_compactlySupported_l2RealForm g μ hμ _ hV hcV
  have hVzero : multiplyRealForm η W = 0 := by
    apply smoothRealForm_eq_of_ae g μ hμ _ 0 hV smoothRealForm_zero
    apply l2Form_ae_eq_of_compact_pairings g μ hμ _ 0 hVL (l2RealForm_zero g.form μ)
    intro B hB hcB
    have heq : formInner g.form (multiplyRealForm η W) B =
        formInner g.form W (multiplyRealForm η B) := by
      rw [formInner_symm g.form W (multiplyRealForm η B)]
      funext y
      rw [formInner_multiplyRealForm_left, formInner_multiplyRealForm_left,
        formInner_symm g.form W B]
    rw [heq, hpair _ (smoothRealForm_multiply η B hη hB)
      (compactlySupportedRealForm_multiply_scalar η hcη B), formInner_zero_left]
    simp only [Pi.zero_apply, integral_zero]
  have hv := congrFun hVzero x
  change η x • W x = 0 at hv
  have hηx : η x = 1 := hηone x (by rw [g.induced_distance_eq_zero.mpr rfl]; norm_num)
  simpa only [hηx, one_smul, Pi.zero_apply] using hv

/-- The original metric codifferential squares to zero on every smooth
form, proved by its actual Green identity and compact form tests. -/
theorem codifferential_square_zero (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M ((k + 1) + 1))
    (hA : SmoothRealForm A) :
    codifferentialRealForm g.form (codifferentialRealForm g.form A) = 0 := by
  have hδA := codifferentialRealForm_smooth g μ hμ A hA
  apply smoothForm_zero_of_compact_pairings g μ hμ _
    (codifferentialRealForm_smooth g μ hμ _ hδA)
  intro B hB hcB
  calc
    _ = ∫ y, formInner g.form B
        (codifferentialRealForm g.form (codifferentialRealForm g.form A)) y ∂μ := by
      rw [formInner_symm]
    _ = ∫ y, formInner g.form (exteriorRealForm B) (codifferentialRealForm g.form A) y ∂μ :=
      (integral_exterior_codifferential g μ hμ B _ hB hδA hcB).symm
    _ = ∫ y, formInner g.form (exteriorRealForm (exteriorRealForm B)) A y ∂μ :=
      (integral_exterior_codifferential g μ hμ _ A (exteriorRealForm_smooth B hB) hA
        (exteriorRealForm_compactlySupported B hB hcB)).symm
    _ = 0 := by
      rw [exterior_square_zero B hB, formInner_zero_left]
      simp only [Pi.zero_apply, integral_zero]

theorem exterior_zero : exteriorRealForm (0 : RealForm M k) = 0 := by
  simpa only [zero_smul] using
    exteriorRealForm_smul (M := M) (k := k) 0 (0 : RealForm M k) smoothRealForm_zero

/-- The actual codifferential commutes with the original Hodge expression
in every allowed degree, including the degree-zero boundary. -/
theorem codifferential_hodge_commute (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M (k + 1)) (hA : SmoothRealForm A) :
    codifferentialRealForm g.form (hodgeRealForm g.form (k + 1) A) =
      hodgeRealForm g.form k (codifferentialRealForm g.form A) := by
  have hδA := codifferentialRealForm_smooth g μ hμ A hA
  have hdδA := exteriorRealForm_smooth _ hδA
  have hδdA := codifferentialRealForm_smooth g μ hμ _ (exteriorRealForm_smooth A hA)
  cases k with
  | zero =>
    simp only [hodgeRealForm]
    rw [codifferentialRealForm_add g μ hμ _ _ hdδA hδdA,
      codifferential_square_zero g μ hμ (exteriorRealForm A) (exteriorRealForm_smooth A hA), add_zero]
  | succ k =>
    simp only [hodgeRealForm]
    rw [codifferentialRealForm_add g μ hμ _ _ hdδA hδdA,
      codifferential_square_zero g μ hμ (exteriorRealForm A) (exteriorRealForm_smooth A hA), add_zero,
      codifferential_square_zero g μ hμ A hA, exterior_zero, zero_add]

end Yau.NodeProofs.P06Aux
