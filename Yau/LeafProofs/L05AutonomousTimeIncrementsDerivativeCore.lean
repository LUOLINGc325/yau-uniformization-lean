import Yau.LeafProofs.L05AutonomousTimeIncrementsFTC

open Set Filter MeasureTheory Metric
open scoped Topology Interval
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L05AutonomousAux

theorem auto_global_dyadic_derivative_properties {a b d A s h : ℝ} (hd : 0 < d) (hab : a+d < b)
    (hA : 0 ≤ A) (hs : 1 < s) {f : ℝ → ℝ} (hf : Continuous f)
    (hSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s)
    (hh : 0 < h) (hhd : h ≤ d/2) :
    ContinuousOn (autoDyadicDerivative f h) (Icc (a+d) b) ∧
      (∀ x∈Icc (a+d) b, ∀ y∈Icc (a+d) b, f y-f x=∫ t in x..y, autoDyadicDerivative f h t) ∧
      (∀ t∈Icc (a+d) b, HasDerivWithinAt f (autoDyadicDerivative f h t) (Icc (a+d) b) t) := by
  have hUniform := auto_dyadic_slope_uniform hd hA hs hSecond hh hhd
  have hCont (k : ℕ) : Continuous (fun t => autoBackwardSlope f t (autoDyadicStep h k)) :=
    (hf.sub (hf.comp (continuous_id.sub continuous_const))).div_const _
  have hV := hUniform.continuousOn (Eventually.of_forall (fun k => (hCont k).continuousOn)).frequently
  have hFTC := auto_uniform_backward_slopes_ftc hh hf hUniform
  exact ⟨hV,hFTC,fun t ht => auto_hasDerivWithinAt_of_ftc hab hV hFTC ht⟩

theorem auto_second_derivative_core {a b d A s : ℝ} (hd : 0 < d) (hab : a+d < b)
    (hA : 0 ≤ A) (hs : 1 < s) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    (hSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond f t h| ≤ A*h^s) :
    ∃ V : ℝ → ℝ, ContinuousOn V (Icc (a+d) b) ∧
      (∀ t∈Icc (a+d) b, ∀ h : ℝ, 0 < h → h ≤ d/2 →
        |autoBackwardSlope f t h-V t| ≤ (1/(1-(1/2 : ℝ)^(s-1)))*A*h^(s-1)) ∧
      (∀ x∈Icc (a+d) b, ∀ y∈Icc (a+d) b, f y-f x=∫ t in x..y, V t) ∧
      (∀ t∈Ioo (a+d) b, HasDerivAt f (V t) t) ∧
      (∀ t∈Icc (a+d) b, HasDerivWithinAt f (V t) (Icc (a+d) b) t) := by
  have hab0 : a ≤ b := by linarith
  let g := autoContinuousExtension hab0 f
  have hg : Continuous g := auto_continuousExtension_continuous hab0 hf
  have hgEq (t : ℝ) (ht : t∈Icc a b) : g t=f t := auto_continuousExtension_eq hab0 f ht
  have hgSecond : ∀ t h : ℝ, 0 < h → a ≤ t-2*h → t ≤ b → |autoRealSecond g t h| ≤ A*h^s := by
    intro t h hh htlo hthi
    unfold autoRealSecond
    rw [hgEq t ⟨by linarith,hthi⟩,hgEq (t-h) ⟨by linarith,by linarith⟩,
      hgEq (t-2*h) ⟨htlo,by linarith⟩]
    exact hSecond t h hh htlo hthi
  let V := autoDyadicDerivative g (d/2)
  have hBase := auto_global_dyadic_derivative_properties hd hab hA hs hg hgSecond (half_pos hd) le_rfl
  have hFTC : ∀ x∈Icc (a+d) b, ∀ y∈Icc (a+d) b, f y-f x=∫ t in x..y, V t := by
    intro x hx y hy
    have h := hBase.2.1 x hx y hy
    rw [hgEq x ⟨by linarith [hx.1],hx.2⟩,hgEq y ⟨by linarith [hy.1],hy.2⟩] at h
    exact h
  refine ⟨V,hBase.1,?_,hFTC,fun t ht => auto_hasDerivAt_of_ftc hab hBase.1 hFTC ht,
    fun t ht => auto_hasDerivWithinAt_of_ftc hab hBase.1 hFTC ht⟩
  intro t ht h hh hhd
  have hOther := auto_global_dyadic_derivative_properties hd hab hA hs hg hgSecond hh hhd
  have hUnique := uniqueDiffOn_Icc hab t ht
  have hEq : autoDyadicDerivative g h t=V t :=
    ((hOther.2.2 t ht).derivWithin hUnique).symm.trans ((hBase.2.2 t ht).derivWithin hUnique)
  have hError := (auto_dyadic_slope_tendsto hd hA hs hgSecond hh hhd ht).2 0
  rw [auto_dyadicStep_zero,pow_zero,mul_one,hEq,autoBackwardSlope,
    hgEq t ⟨by linarith [ht.1],ht.2⟩,hgEq (t-h) ⟨by linarith [ht.1],by linarith [ht.2]⟩] at hError
  change |(f t-f (t-h))/h-V t| ≤ _
  convert hError using 1 <;> ring

end Yau.LeafProofs.L05AutonomousAux
