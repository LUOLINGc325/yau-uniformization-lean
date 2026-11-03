import Yau.Proofs.P06WeakDDbarCurrentAdjoint

noncomputable section
open MeasureTheory Filter
open scoped Manifold Topology ContDiff Matrix

namespace Yau.NodeProofs.P06Aux.WeakCurrent
open Yau Yau.LeafProofs Yau.LeafProofs.L03 Yau.NodeProofs.G04Aux
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {M : ComplexManifold n}

/-- A genuine compact smooth scalar cutoff equals one on a neighborhood of
an arbitrary compact set. The cutoff is constructed in the original metric. -/
theorem exists_compact_smooth_one_near (g : SmoothMetric M) {K : Set M.Carrier}
    (hK : IsCompact K) :
    ∃ η : M.Carrier → ℝ, SmoothFn η ∧ HasCompactSupport η ∧
      ∀ x ∈ K, ∀ᶠ y in 𝓝 x, η y = 1 := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨c, _⟩ := hne
    obtain ⟨b, hb⟩ := hK.bddAbove_image (L12Aux.continuous_distFrom g c).continuousOn
    let r : ℝ := max b 0 + 1
    have hr : 0 < r := by dsimp only [r]; linarith [le_max_right b 0]
    obtain ⟨η, hη, hcη, _, hηone, _⟩ := L18Aux.exists_smooth_compact_cutoff g c hr
      (show r < r + 1 by linarith)
    refine ⟨η, hη, hcη, ?_⟩
    intro x hx
    have hxlt : inducedDistance g.form c x < r := by
      have h := hb ⟨x, hx, rfl⟩
      change inducedDistance g.form c x ≤ b at h
      dsimp only [r]
      linarith [le_max_left b 0]
    filter_upwards [(L12Aux.continuous_distFrom g c).continuousAt.eventually
      (Iio_mem_nhds hxlt)] with y hy
    exact hηone y hy.le
  · refine ⟨0, ?_, HasCompactSupport.zero, ?_⟩
    · intro c; exact contDiffOn_const
    · intro x hx; exact False.elim (hne ⟨x, hx⟩)

/-- The actual exterior derivative is local on smooth forms. -/
theorem exteriorRealForm_congr_near (A B : RealForm M k)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (x : M.Carrier)
    (heq : ∀ᶠ y in 𝓝 x, A y = B y) :
    exteriorRealForm A x = exteriorRealForm B x := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hlocal := formComponents_eventuallyEq_of_eventuallyEq x hz (by simpa only [hx] using heq)
  have hd := exteriorComponents_congr_nhds hlocal
  have he : (exteriorRealForm A - exteriorRealForm B) x = 0 := by
    apply (formComponents_center_eq_zero_iff _ x).mp
    funext I
    change formComponents (exteriorRealForm A) x (chartPt x x) I -
      formComponents (exteriorRealForm B) x (chartPt x x) I = 0
    rw [exteriorRealForm_represents A hA x _ hz I,
      exteriorRealForm_represents B hB x _ hz I, congrFun hd I, sub_self]
  exact sub_eq_zero.mp he

/-- Green's identity also holds when the test in the higher degree has
compact support. No compactness of the smooth first input is assumed. -/
theorem integral_exterior_codifferential_right (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (A : RealForm M k) (B : RealForm M (k + 1))
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ x, formInner g.form (exteriorRealForm A) B x ∂μ) =
      ∫ x, formInner g.form A (codifferentialRealForm g.form B) x ∂μ := by
  obtain ⟨η, hη, hcη, hηone⟩ := exists_compact_smooth_one_near g hcB
  let T := multiplyRealForm η A
  have hT : SmoothRealForm T := smoothRealForm_multiply η A hη hA
  have hcT : CompactlySupportedRealForm T := compactlySupportedRealForm_multiply_scalar η hcη A
  have he := integral_exterior_codifferential g μ hμ T B hT hB hcT
  calc
    _ = ∫ x, formInner g.form (exteriorRealForm T) B x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : B x = 0
      · rw [formInner_symm g.form (exteriorRealForm A) B,
          formInner_symm g.form (exteriorRealForm T) B]
        rw [formInner_eq_zero_of_left_eq_zero g.form B _ x hx,
          formInner_eq_zero_of_left_eq_zero g.form B _ x hx]
      · have hn : ∀ᶠ y in 𝓝 x, T y = A y := by
          filter_upwards [hηone x (subset_closure hx)] with y hy
          simp only [T, multiplyRealForm, hy, one_smul]
        exact formInner_congr_at g.form (exteriorRealForm_congr_near T A hT hA x hn).symm rfl
    _ = ∫ x, formInner g.form T (codifferentialRealForm g.form B) x ∂μ := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : codifferentialRealForm g.form B x = 0
      · rw [formInner_symm g.form T _, formInner_symm g.form A _]
        rw [formInner_eq_zero_of_left_eq_zero g.form _ _ x hx,
          formInner_eq_zero_of_left_eq_zero g.form _ _ x hx]
      · have hxK := codifferentialRealForm_support_subset g μ hμ B hB (subset_closure hx)
        have hηx := (hηone x hxK).self_of_nhds
        simp only [T, formInner_multiplyRealForm_left, hηx, one_mul]

/-- Two genuine Green identities and skew-adjointness of J give the scalar
adjoint of dd, including its actual factor 1/2 and its positive sign. -/
theorem integral_dd_eq_adjoint (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ x, formInner g.form (ddRealForm f) B x ∂μ) =
      ∫ x, f x * ddAdjointScalar g.form B x ∂μ := by
  have hδB := codifferentialRealForm_smooth g μ hμ B hB
  have hcδB := codifferentialRealForm_compactlySupported g μ hμ B hB hcB
  have hJB := jPullbackOne_smooth _ hδB
  have hcJB := jPullbackOne_compact _ hcδB
  have he₁ := integral_exterior_codifferential_right g μ hμ (jDifferential f) B
    (jDifferential_smooth f hf) hB hcB
  have he₂ := integral_exterior_codifferential_right g μ hμ (scalarForm f)
    (jPullbackForm (codifferentialRealForm g.form B)) (scalarForm_smooth f hf) hJB hcJB
  calc
    _ = (-(1 / 2 : ℝ)) * ∫ x, formInner g.form
        (exteriorRealForm (jDifferential f)) B x ∂μ := by
      simp only [ddRealForm, formInner_smul_left, Pi.smul_apply, smul_eq_mul, integral_const_mul]
    _ = (-(1 / 2 : ℝ)) * ∫ x, formInner g.form
        (jDifferential f) (codifferentialRealForm g.form B) x ∂μ := by rw [he₁]
    _ = (1 / 2 : ℝ) * ∫ x, formInner g.form (exteriorRealForm (scalarForm f))
        (jPullbackForm (codifferentialRealForm g.form B)) x ∂μ := by
      simp only [jDifferential, formInner_jPullbackOne_skew, integral_neg]
      ring
    _ = (1 / 2 : ℝ) * ∫ x, formInner g.form (scalarForm f)
        (codifferentialRealForm g.form (jPullbackForm (codifferentialRealForm g.form B))) x ∂μ := by
      rw [he₂]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [formInner_scalar]
      dsimp only [ddAdjointScalar]
      ring

end Yau.NodeProofs.P06Aux.WeakCurrent
