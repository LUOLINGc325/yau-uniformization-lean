import Yau.LeafProofs.L21WeakEquationDifferentiation

/-! Local weak derivatives form a complex linear space. Smooth local
functions have their literal Fréchet directional derivatives. -/

open MeasureTheory
open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

def ofRealTest {O : Set (X n)} (ψ : X n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ O) : CompactTest O :=
  ⟨fun x => (ψ x : ℂ), Complex.ofRealCLM.contDiff.comp hψ,
    hcψ.comp_left Complex.ofReal_zero, (tsupport_comp_subset Complex.ofReal_zero ψ).trans hsψ⟩

theorem locallyL2On_of_continuousOn {O : Set (X n)} {f : X n → ℂ}
    (hf : ContinuousOn f O) : LocallyL2On f O := by
  intro K hK hKO
  have hfK := hf.mono hKO
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hfK
  letI : IsFiniteMeasure ((Yau.lebesgueC n).restrict K) := isFiniteMeasure_restrict.mpr (by
    rw [Yau.LeafProofs.lebesgueC_eq_volume]
    exact hK.measure_lt_top.ne)
  have hm : MemLp f ⊤ ((Yau.lebesgueC n).restrict K) := memLp_top_of_bound
    (hfK.aestronglyMeasurable hK.measurableSet) B
    ((ae_restrict_mem hK.measurableSet).mono fun x hx => hB x hx)
  exact hm.mono_exponent (by simp)

theorem complexWeakDerivativeOn_smooth {O : Set (X n)} (hO : IsOpen O)
    {u : X n → ℂ} (hu : ContDiffOn ℝ ∞ u O) (v : X n) :
    ComplexWeakDerivativeOn O u (fun x => fderiv ℝ u x v) v := by
  intro ψ hψ hcψ hsψ
  have hh := integral_local_mul_compact_fderiv hO (hu.of_le (by simp))
    ((ofRealTest ψ hψ hcψ hsψ).property.1.of_le (by simp))
    (ofRealTest ψ hψ hcψ hsψ).property.2.1 (ofRealTest ψ hψ hcψ hsψ).property.2.2 v
  change (∫ x, u x * fderiv ℝ (fun y => (ψ y : ℂ)) x v ∂Yau.lebesgueC n) =
    -(∫ x, fderiv ℝ u x v * (ψ x : ℂ) ∂Yau.lebesgueC n) at hh
  simpa only [fderiv_ofReal_apply (hψ.differentiable (by simp) _)] using hh

theorem complexWeakDerivativeOn_zero (O : Set (X n)) (v : X n) :
    ComplexWeakDerivativeOn O (fun _ => 0) (fun _ => 0) v := by
  intro ψ _ _ _
  simp

theorem complexWeakDerivativeOn_add {O : Set (X n)} (hO : IsOpen O)
    {u g u' g' : X n → ℂ} {v : X n}
    (hu : LocallyL2On u O) (hg : LocallyL2On g O)
    (hu' : LocallyL2On u' O) (hg' : LocallyL2On g' O)
    (h : ComplexWeakDerivativeOn O u g v) (h' : ComplexWeakDerivativeOn O u' g' v) :
    ComplexWeakDerivativeOn O (fun x => u x + u' x) (fun x => g x + g' x) v := by
  intro ψ hψ hcψ hsψ
  let ψC := ofRealTest ψ hψ hcψ hsψ
  have intD (f : X n → ℂ) (hf : LocallyL2On f O) :
      Integrable (fun x => f x * (fderiv ℝ ψ x v : ℂ)) (Yau.lebesgueC n) := by
    have hh := locallyL2On_test_integrable hO hf (directionalTest ψC v)
    change Integrable (fun x => f x * fderiv ℝ (fun y => (ψ y : ℂ)) x v) (Yau.lebesgueC n) at hh
    simpa only [fderiv_ofReal_apply (hψ.differentiable (by simp) _)] using hh
  have intV (f : X n → ℂ) (hf : LocallyL2On f O) :
      Integrable (fun x => f x * (ψ x : ℂ)) (Yau.lebesgueC n) :=
    locallyL2On_test_integrable hO hf ψC
  simp only [add_mul]
  rw [integral_add (intD u hu) (intD u' hu'), integral_add (intV g hg) (intV g' hg'),
    h ψ hψ hcψ hsψ, h' ψ hψ hcψ hsψ]
  ring

theorem complexWeakDerivativeOn_neg {O : Set (X n)} {u g : X n → ℂ} {v : X n}
    (h : ComplexWeakDerivativeOn O u g v) :
    ComplexWeakDerivativeOn O (fun x => -u x) (fun x => -g x) v := by
  intro ψ hψ hcψ hsψ
  simp only [neg_mul, integral_neg, h ψ hψ hcψ hsψ]

theorem complexWeakDerivativeOn_mono {O V : Set (X n)} {u g : X n → ℂ} {v : X n}
    (h : ComplexWeakDerivativeOn O u g v) (hVO : V ⊆ O) :
    ComplexWeakDerivativeOn V u g v := fun ψ hψ hcψ hsψ => h ψ hψ hcψ (hsψ.trans hVO)

end Yau.LeafProofs.L21Aux
