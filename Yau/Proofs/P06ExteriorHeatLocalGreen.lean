import Yau.Proofs.P06ExteriorHeatSemigroup

noncomputable section
open MeasureTheory Filter Set
open scoped Topology InnerProductSpace ContDiff

namespace Yau.NodeProofs.P06Aux.ExteriorHeat
open Yau Yau.LeafProofs
variable {n k : ℕ} {M : ComplexManifold n}

/-- Actual exterior differentiation is local. -/
theorem exteriorRealForm_eq_at_of_eventuallyEq {A B : RealForm M k}
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (y : M.Carrier)
    (hAB : ∀ᶠ x in 𝓝 y, A x = B x) :
    L03.exteriorRealForm A y = L03.exteriorRealForm B y := by
  apply sub_eq_zero.mp
  apply (L03.formComponents_center_eq_zero_iff
    (L03.exteriorRealForm A - L03.exteriorRealForm B) y).mp
  funext I
  change formComponents (L03.exteriorRealForm A) y (chartPt y y) I -
    formComponents (L03.exteriorRealForm B) y (chartPt y y) I = 0
  have hz : chartPt y y ∈ chartTarget y := mem_extChartAt_target y
  rw [L03.exteriorRealForm_represents A hA y _ hz I,
    L03.exteriorRealForm_represents B hB y _ hz I]
  apply sub_eq_zero.mpr
  apply congrFun (L03.exteriorComponents_congr_nhds ?_) I
  apply L03.formComponents_eventuallyEq_of_eventuallyEq y hz
  have hi : chartInv y (chartPt y y) = y :=
    (extChartAt (ComplexModel n) y).left_inv (mem_extChartAt_source y)
  simpa only [hi] using hAB

/-- Green with only the test form compact: no global L² hypothesis on W. -/
theorem integral_exterior_codifferential_local
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (W : RealForm M k) (B : RealForm M (k+1))
    (hW : SmoothRealForm W) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ y, formInner g.form (L03.exteriorRealForm W) B y ∂μ) =
      ∫ y, formInner g.form W (L03.codifferentialRealForm g.form B) y ∂μ := by
  letI : LocallyCompactSpace M.Carrier := L12Aux.manifold_locallyCompact M
  obtain ⟨K,hK,hBK⟩ := exists_compact_superset hcB
  obtain ⟨ζ,hζ,hcζ,hζK⟩ := L03.exists_smooth_compact_scalar_one_on hK
  let V := L03.multiplyRealForm ζ W
  have hV : SmoothRealForm V := L03.smoothRealForm_multiply ζ W hζ hW
  have hcV : CompactlySupportedRealForm V := L03.compactlySupportedRealForm_multiply_scalar ζ hcζ W
  have hVW (y : M.Carrier) (hy : y ∈ closure {x | B x ≠ 0}) : V y = W y := by
    change ζ y • W y = W y
    rw [hζK y (interior_subset (hBK hy)),one_smul]
  have hdVW (y : M.Carrier) (hy : y ∈ closure {x | B x ≠ 0}) :
      L03.exteriorRealForm V y = L03.exteriorRealForm W y := by
    apply exteriorRealForm_eq_at_of_eventuallyEq hV hW y
    filter_upwards [isOpen_interior.mem_nhds (hBK hy)] with x hx
    change ζ x • W x = W x
    rw [hζK x (interior_subset hx),one_smul]
  have hleft : formInner g.form (L03.exteriorRealForm V) B =
      formInner g.form (L03.exteriorRealForm W) B := by
    funext y
    by_cases hy : y ∈ closure {x | B x ≠ 0}
    · exact L03.formInner_congr_at g.form (hdVW y hy) rfl
    · have hBy : B y = 0 := by by_contra h; exact hy (subset_closure h)
      calc
        _ = formInner g.form (L03.exteriorRealForm V) 0 y := L03.formInner_congr_at g.form rfl hBy
        _ = 0 := congrFun (L03.formInner_zero_right g.form _) y
        _ = formInner g.form (L03.exteriorRealForm W) B y := by
          rw [L03.formInner_congr_at g.form (A := L03.exteriorRealForm W) (B' := (0 : RealForm M (k+1))) rfl hBy]
          exact (congrFun (L03.formInner_zero_right g.form _) y).symm
  have hright : formInner g.form V (L03.codifferentialRealForm g.form B) =
      formInner g.form W (L03.codifferentialRealForm g.form B) := by
    funext y
    by_cases hy : y ∈ closure {x | B x ≠ 0}
    · exact L03.formInner_congr_at g.form (hVW y hy) rfl
    · have hδy : L03.codifferentialRealForm g.form B y = 0 := by
        by_contra h
        exact hy ((L03.codifferentialRealForm_support_subset g μ hμ B hB) (subset_closure h))
      calc
        _ = formInner g.form V 0 y := L03.formInner_congr_at g.form rfl hδy
        _ = 0 := congrFun (L03.formInner_zero_right g.form _) y
        _ = formInner g.form W (L03.codifferentialRealForm g.form B) y := by
          rw [L03.formInner_congr_at g.form (A := W) (B' := (0 : RealForm M k)) rfl hδy]
          exact (congrFun (L03.formInner_zero_right g.form _) y).symm
  have he := L03.integral_exterior_codifferential g μ hμ V B hV hB hcV
  rwa [hleft,hright] at he

/-- Smooth distributional closedness is the literal all-chart closedness. -/
theorem closedRealForm_of_codifferential_pairings
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (W : RealForm M k) (hW : SmoothRealForm W)
    (hp : ∀ (B : RealForm M (k+1)), SmoothRealForm B → CompactlySupportedRealForm B →
      (∫ y, formInner g.form W (L03.codifferentialRealForm g.form B) y ∂μ) = 0) :
    ClosedRealForm W := by
  have he : L03.exteriorRealForm W = 0 := by
    apply smoothForm_zero_of_compact_pairings g μ hμ _ (L03.exteriorRealForm_smooth W hW)
    intro B hB hcB
    rw [integral_exterior_codifferential_local g μ hμ W B hW hB hcB]
    exact hp B hB hcB
  intro x z hz I
  have hrep := L03.exteriorRealForm_represents W hW x z hz I
  rw [he,L03.formComponents_zero] at hrep
  exact hrep.symm

end Yau.NodeProofs.P06Aux.ExteriorHeat
