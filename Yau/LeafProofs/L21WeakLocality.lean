import Yau.LeafProofs.L21WeakProducts

/-! Locality, uniqueness and commutation of the actual weak derivatives.
The local first-order gain therefore applies to the original function on
every relatively compact inner region. -/

open MeasureTheory Filter
open scoped ContDiff Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ}

theorem complexWeakDerivativeOn_congr {O : Set (X n)} {u g u' g' : X n → ℂ} {v : X n}
    (h : ComplexWeakDerivativeOn O u g v)
    (hu : ∀ x ∈ O, u' x = u x) (hg : ∀ x ∈ O, g' x = g x) :
    ComplexWeakDerivativeOn O u' g' v := by
  intro ψ hψ hcψ hsψ
  have hL : (fun x => u' x * (fderiv ℝ ψ x v : ℂ)) =
      fun x => u x * (fderiv ℝ ψ x v : ℂ) := by
    funext x
    by_cases hx : x ∈ O
    · rw [hu x hx]
    · have hn : x ∉ tsupport ψ := fun hh => hx (hsψ hh)
      simp [fderiv_of_notMem_tsupport ℝ hn]
  have hR : (fun x => g' x * (ψ x : ℂ)) = fun x => g x * (ψ x : ℂ) := by
    funext x
    by_cases hx : x ∈ O
    · rw [hg x hx]
    · have hn : x ∉ tsupport ψ := fun hh => hx (hsψ hh)
      simp [image_eq_zero_of_notMem_tsupport hn]
  rw [hL, hR]
  exact h ψ hψ hcψ hsψ

theorem complex_ae_eq_of_test_integrals_eq {O : Set (X n)} (hO : IsOpen O)
    {u g : X n → ℂ} (hu : LocallyL2On u O) (hg : LocallyL2On g O)
    (hp : ∀ (ψ : X n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ O →
      (∫ x, u x * (ψ x : ℂ) ∂Yau.lebesgueC n) =
        ∫ x, g x * (ψ x : ℂ) ∂Yau.lebesgueC n) :
    u =ᵐ[(Yau.lebesgueC n).restrict O] g := by
  apply (ae_restrict_iff' hO.measurableSet).mpr
  have hzero := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((locallyIntegrableOn_of_locallyL2On hO hu).sub (locallyIntegrableOn_of_locallyL2On hO hg))
    (fun ψ hψ hcψ hsψ => by
      let ψC : CompactTest O :=
        ⟨fun x => (ψ x : ℂ), Complex.ofRealCLM.contDiff.comp hψ,
          hcψ.comp_left Complex.ofReal_zero, (tsupport_comp_subset Complex.ofReal_zero ψ).trans hsψ⟩
      have hfu := locallyL2On_test_integrable hO hu ψC
      have hfg := locallyL2On_test_integrable hO hg ψC
      have he : (fun x => ψ x • (u x - g x)) =
          fun x => u x * (ψ x : ℂ) - g x * (ψ x : ℂ) := by
        funext x
        simp only [Complex.real_smul, smul_eq_mul]
        ring
      change (∫ x, ψ x • (u x - g x) ∂Yau.lebesgueC n) = 0
      rw [he, integral_sub hfu hfg, hp ψ hψ hcψ hsψ, sub_self])
  filter_upwards [hzero] with x hx hxin
  exact sub_eq_zero.mp (hx hxin)

theorem complexWeakDerivativeOn_unique {O : Set (X n)} (hO : IsOpen O)
    {u g h : X n → ℂ} {v : X n}
    (hg : LocallyL2On g O) (hh : LocallyL2On h O)
    (h1 : ComplexWeakDerivativeOn O u g v) (h2 : ComplexWeakDerivativeOn O u h v) :
    g =ᵐ[(Yau.lebesgueC n).restrict O] h := by
  apply complex_ae_eq_of_test_integrals_eq hO hg hh
  intro ψ hψ hcψ hsψ
  exact neg_injective ((h1 ψ hψ hcψ hsψ).symm.trans (h2 ψ hψ hcψ hsψ))

theorem exists_inner_weak_gradient {O V : Set (X n)} (hO : IsOpen O)
    (hcV : IsCompact (closure V)) (hVO : closure V ⊆ O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    (hsmall : ∀ x ∈ O, Yau.LeafCandidates.matrixOpNorm (A x) ≤ 1 / 2)
    (u : X n → ℂ) (w : X n → Fin n → ℂ)
    (hu : LocallyL2On u O) (hw : ∀ i, LocallyL2On (fun x => w x i) O)
    (heq : DbarWeakOn A u w O) :
    ∃ G : X n → Yau.RIdx n → ℂ,
      (∀ a, MemLp (fun x => G x a) 2 (Yau.lebesgueC n)) ∧
      ∀ a, ComplexWeakDerivativeOn V u (fun x => G x a) (Yau.realVec a) := by
  obtain ⟨χ, hχ, hcχ, hsχ, _hχrange, hχV⟩ :=
    Yau.LeafProofs.L14Aux.exists_model_open_cutoff hO hcV hVO
  obtain ⟨L, G, _hcL, _hLO, hG, _hsG, hWeak, _hEnergy⟩ :=
    local_weak_first_order_gain hO hA hsmall u w hu hw heq χ hχ hcχ hsχ
  refine ⟨G, hG, fun a => ?_⟩
  apply complexWeakDerivativeOn_congr (complexWeakDerivativeOn_of_global (hWeak a)) ?_ (fun _ _ => rfl)
  intro x hx
  rw [(hχV x (subset_closure hx)).1, Complex.ofReal_one, one_mul]

theorem real_second_directional_commute {ψ : X n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (x v w : X n) :
    fderiv ℝ (fun y => fderiv ℝ ψ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ ψ y w) x v := by
  have hd := (hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hd (differentiableAt_const v),
    fderiv_clm_apply hd (differentiableAt_const w)]
  simpa using ((hψ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)).eq w v

theorem complex_weak_derivatives_commute {O : Set (X n)}
    {u uv uw h : X n → ℂ} {v w : X n}
    (hv : ComplexWeakDerivativeOn O u uv v) (hw : ComplexWeakDerivativeOn O u uw w)
    (hvw : ComplexWeakDerivativeOn O uv h w) : ComplexWeakDerivativeOn O uw h v := by
  intro ψ hψ hcψ hsψ
  have hdψ (a : X n) : ContDiff ℝ ∞ (fun x => fderiv ℝ ψ x a) :=
    (hψ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have h1 := hv _ (hdψ w) (hcψ.fderiv_apply ℝ w) ((tsupport_fderiv_apply_subset ℝ w).trans hsψ)
  have h2 := hw _ (hdψ v) (hcψ.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hsψ)
  simp only [real_second_directional_commute hψ _ w v] at h1
  have he : (∫ x, uv x * (fderiv ℝ ψ x w : ℂ) ∂Yau.lebesgueC n) =
      ∫ x, uw x * (fderiv ℝ ψ x v : ℂ) ∂Yau.lebesgueC n :=
    neg_injective (h1.symm.trans h2)
  exact he.symm.trans (hvw ψ hψ hcψ hsψ)

end Yau.LeafProofs.L21Aux
