import Yau.Proofs.P06DDbarHeatSemigroup

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.DDbarHeat
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n k : ℕ} {M : ComplexManifold n}

theorem codifferential_congr_near (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M (k+1))
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (x : M.Carrier)
    (heq : ∀ᶠ y in 𝓝 x, A y = B y) :
    codifferentialRealForm g.form A x = codifferentialRealForm g.form B x := by
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  have hlocal := formComponents_eventuallyEq_of_eventuallyEq x hz (by simpa only [hx] using heq)
  have hd := codifferentialComponents_congr_nhds g.form x hlocal
  have he : (codifferentialRealForm g.form A - codifferentialRealForm g.form B) x = 0 := by
    apply (formComponents_center_eq_zero_iff _ x).mp
    funext I
    change formComponents (codifferentialRealForm g.form A) x (chartPt x x) I -
      formComponents (codifferentialRealForm g.form B) x (chartPt x x) I = 0
    rw [codifferentialRealForm_represents g μ hμ A hA x _ hz I,
      codifferentialRealForm_represents g μ hμ B hB x _ hz I, congrFun hd I, sub_self]
  exact sub_eq_zero.mp he

theorem adjointScalar_congr_near (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A B : RealForm M 2)
    (hA : SmoothRealForm A) (hB : SmoothRealForm B) (x : M.Carrier)
    (heq : ∀ᶠ y in 𝓝 x, A y = B y) :
    WeakCurrent.ddAdjointScalar g.form A x = WeakCurrent.ddAdjointScalar g.form B x := by
  have hδ : ∀ᶠ y in 𝓝 x, codifferentialRealForm g.form A y = codifferentialRealForm g.form B y :=
    heq.eventually_nhds.mono fun y hy => codifferential_congr_near g μ hμ A B hA hB y hy
  have hJ : ∀ᶠ y in 𝓝 x,
      jPullbackForm (codifferentialRealForm g.form A) y =
        jPullbackForm (codifferentialRealForm g.form B) y := by
    filter_upwards [hδ] with y hy
    simp only [jPullbackForm, hy]
  have he := codifferential_congr_near g μ hμ _ _
    (WeakCurrent.jPullbackOne_smooth _ (codifferentialRealForm_smooth g μ hμ A hA))
    (WeakCurrent.jPullbackOne_smooth _ (codifferentialRealForm_smooth g μ hμ B hB)) x hJ
  simp only [WeakCurrent.ddAdjointScalar, WeakCurrent.scalarValue, he]

theorem exists_cutoff_one_near (g : SmoothMetric M) {K : Set M.Carrier} (hK : IsCompact K) :
    ∃ η : M.Carrier → ℝ, SmoothFn η ∧ HasCompactSupport η ∧
      (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ x ∈ K, ∀ᶠ y in 𝓝 x, η y = 1 := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨c,_⟩ := hne
    obtain ⟨b,hb⟩ := hK.bddAbove_image (L12Aux.continuous_distFrom g c).continuousOn
    let r : ℝ := max b 0 + 1
    have hr : 0 < r := by dsimp only [r]; linarith [le_max_right b 0]
    obtain ⟨η,hη,hcη,hηrange,hηone,_⟩ := L18Aux.exists_smooth_compact_cutoff g c hr
      (show r < r+1 by linarith)
    refine ⟨η,hη,hcη,hηrange,?_⟩
    intro x hx
    have hxlt : inducedDistance g.form c x < r := by
      have h := hb ⟨x,hx,rfl⟩
      change inducedDistance g.form c x ≤ b at h
      dsimp only [r]
      linarith [le_max_left b 0]
    filter_upwards [(L12Aux.continuous_distFrom g c).continuousAt.eventually (Iio_mem_nhds hxlt)] with y hy
    exact hηone y hy.le
  · refine ⟨0,(fun _ => contDiffOn_const),HasCompactSupport.zero,?_,?_⟩
    · intro x; exact ⟨le_rfl,zero_le_one⟩
    · intro x hx; exact False.elim (hne ⟨x,hx⟩)

theorem current_cutoff_independent (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ)
    (U : RealForm M 2) (hU : SmoothRealForm U)
    (η ξ : M.Carrier → ℝ) (hη : SmoothFn η) (hξ : SmoothFn ξ)
    (hηone : ∀ x ∈ tsupport f, ∀ᶠ y in 𝓝 x, η y = 1)
    (hξone : ∀ x ∈ tsupport f, ∀ᶠ y in 𝓝 x, ξ y = 1) (x : M.Carrier) :
    f x * WeakCurrent.ddAdjointScalar g.form (multiplyRealForm η U) x =
      f x * WeakCurrent.ddAdjointScalar g.form (multiplyRealForm ξ U) x := by
  by_cases hx : f x = 0
  · simp only [hx,zero_mul]
  · have heq : ∀ᶠ y in 𝓝 x, multiplyRealForm η U y = multiplyRealForm ξ U y := by
      filter_upwards [hηone x (subset_tsupport _ hx),hξone x (subset_tsupport _ hx)] with y hy hz
      simp only [multiplyRealForm,hy,hz]
    exact congrArg (fun a : ℝ => f x * a) (adjointScalar_congr_near g μ hμ _ _
      (smoothRealForm_multiply η U hη hU) (smoothRealForm_multiply ξ U hξ hU) x heq)

end Yau.NodeProofs.P06Aux.DDbarHeat
