import spec.CHAIN.CONTRACTS

/-! An actual smooth scalar curve and continuous right-hand side extend
their interior differential equation to both faces of the original slab. -/
noncomputable section
open Set
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem eqOn_closed_interval_of_interior {a b : ℝ} (hab : a < b)
    {f g : ℝ → F} (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (hfg : EqOn f g (Ioo a b)) :
    EqOn f g (Icc a b) := by
  apply hfg.of_subset_closure hf hg Ioo_subset_Icc_self
  rw [closure_Ioo hab.ne]

theorem closed_interval_ode_of_interior {a b : ℝ} (hab : a < b)
    {f g : ℝ → F} (hf : ContDiffOn ℝ ∞ f (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hode : ∀ t ∈ Ioo a b, HasDerivAt f (g t) t) :
    ∀ t ∈ Icc a b, HasDerivWithinAt f (g t) (Icc a b) t := by
  have hUnique := uniqueDiffOn_Icc hab
  have hderiv : ContinuousOn (derivWithin f (Icc a b)) (Icc a b) :=
    hf.continuousOn_derivWithin hUnique (by simp)
  have heq : EqOn (derivWithin f (Icc a b)) g (Icc a b) :=
    eqOn_closed_interval_of_interior hab hderiv hg (fun t ht =>
      (hode t ht).hasDerivWithinAt.derivWithin (hUnique t ⟨ht.1.le, ht.2.le⟩))
  intro t ht
  rw [← heq ht]
  exact (hf t ht).differentiableWithinAt (by simp) |>.hasDerivWithinAt

end Yau.NodeProofs.F01Aux
