import Yau.Proofs.P06DDbarHeatLocality

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Yau.NodeProofs.P06Aux.DDbarHeat
open Yau Yau.LeafProofs Yau.LeafProofs.L03 G04Aux
variable {n k : ℕ} {M : ComplexManifold n}

theorem continuous_compact_scalar_l2 (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (f : M.Carrier → ℝ)
    (hf : Continuous f) (hcf : HasCompactSupport f) : L2RealForm g.form μ (scalarForm f) := by
  letI : IsLocallyFiniteMeasure μ := L18Aux.riemannianVolume_locallyFinite g μ hμ
  refine ⟨fun x I => hf.aestronglyMeasurable.mono_measure Measure.restrict_le_self, ?_⟩
  have hi : Integrable (fun x => f x * f x) μ :=
    (hf.mul hf).integrable_of_hasCompactSupport hcf.mul_left
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun x => formNormSq_nonneg g.form (scalarForm f) x))).mp
  change HasFiniteIntegral (fun x => formNormSq g.form (scalarForm f) x) μ
  simpa only [scalarForm_normSq, pow_two] using hi.2

theorem multiplyHilbert_actual (g : SmoothMetric M) (μ : Measure M.Carrier)
    (η : M.Carrier → ℝ) (hηm : AEStronglyMeasurable η μ)
    (C : ℝ) (hC : 0 ≤ C) (hη : ∀ x, |η x| ≤ C)
    (A : RealForm M k) (hA : L2RealForm g.form μ A) :
    multiplyL2FormHilbert g μ η hηm C hC hη (realizeActualForm g μ A hA) =
      realizeActualForm g μ (multiplyRealForm η A)
        (l2RealForm_multiply_bounded g μ η hηm C hC hη A hA) := by
  exact multiplyL2FormHilbert_realize g μ η hηm C hC hη (L2FormSpace.ofSection A hA)

theorem ddForm_support (A : RealForm M 0) (hA : SmoothRealForm A) :
    closure {x | ddForm A x ≠ 0} ⊆ closure {x | A x ≠ 0} := by
  apply (dd_support _ (WeakCurrent.scalarValue_smooth A hA)).trans
  apply closure_mono
  intro x hx hz
  apply hx
  change A x Fin.elim0 = 0
  rw [hz]
  rfl

/-- A fixed bounded multiplier turns the adjoint graph relation into a legitimate
localized current pairing. No global L2 assertion about Q(U) is used. -/
theorem localized_adjoint_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (b : L2FormHilbert g μ 2) (q : L2FormHilbert g μ 0)
    (hbq : (b,q) ∈ (closedDDbar g μ hμ).adjoint.graph)
    (U : RealForm M 2) (hU : SmoothRealForm U) (hUL2 : L2RealForm g.form μ U)
    (hUrep : realizeActualForm g μ U hUL2 = b)
    (f : M.Carrier → ℝ) (hf : L2RealForm g.form μ (scalarForm f))
    (ξ : M.Carrier → ℝ) (hξ : SmoothFn ξ) (hcξ : HasCompactSupport ξ)
    (hrange : ∀ x, ξ x ∈ Set.Icc (0 : ℝ) 1)
    (hξone : ∀ x ∈ tsupport f, ∀ᶠ y in 𝓝 x, ξ y = 1)
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hηone : ∀ x ∈ tsupport ξ, ∀ᶠ y in 𝓝 x, η y = 1) :
    inner ℝ (realizeActualForm g μ (scalarForm f) hf) q =
      ∫ x, f x * WeakCurrent.ddAdjointScalar g.form (multiplyRealForm η U) x ∂μ := by
  have hm := (L18Aux.continuous_of_smoothFn hξ).aestronglyMeasurable (μ := μ)
  have hbound : ∀ x, |ξ x| ≤ 1 := fun x => by rw [abs_of_nonneg (hrange x).1]; exact (hrange x).2
  let P := multiplyL2FormHilbert (k := 0) g μ ξ hm 1 zero_le_one hbound
  let V := multiplyRealForm η U
  have hV : SmoothRealForm V := smoothRealForm_multiply η U hη hU
  have hcV : CompactlySupportedRealForm V := compactlySupportedRealForm_multiply_scalar η hcη U
  let qV := realizeActualForm g μ (adjointForm g.form V) (adjointForm_l2 g μ hμ V hV hcV)
  have hz : P (q-qV) = 0 := by
    apply hilbert_zero_of_compact_form_pairings g μ hμ
    intro A hA hcA
    rw [multiplyL2FormHilbert_inner_symm, inner_sub_left]
    change inner ℝ q (P (realizeActualForm g μ A _)) -
      inner ℝ qV (P (realizeActualForm g μ A _)) = 0
    rw [sub_eq_zero,real_inner_comm (P (realizeActualForm g μ A _)) q,
      real_inner_comm (P (realizeActualForm g μ A _)) qV]
    have hξA := smoothRealForm_multiply ξ A hξ hA
    have hcξA := compactlySupportedRealForm_multiply_scalar ξ hcξ A
    rw [show P (realizeActualForm g μ A _) =
      realizeActualForm g μ (multiplyRealForm ξ A)
        (smooth_compactlySupported_l2RealForm g μ hμ _ hξA hcξA) from
          multiplyHilbert_actual g μ ξ hm 1 zero_le_one hbound A _]
    have he := (ddAdjointGraph_iff g μ hμ b q).mp hbq _ _
      (ddGraph_core g μ hμ _ hξA hcξA)
    change inner ℝ (realizeActualForm g μ (ddForm (multiplyRealForm ξ A)) _) b =
      inner ℝ (realizeActualForm g μ (multiplyRealForm ξ A) _) q at he
    rw [← he,← hUrep,realizeActualForm_inner]
    change _ = inner ℝ (realizeActualForm g μ (multiplyRealForm ξ A) _)
      (realizeActualForm g μ (adjointForm g.form V) _)
    rw [realizeActualForm_inner,← integral_ddForm_adjoint g μ hμ _ hξA V hV hcV]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : ddForm (multiplyRealForm ξ A) x = 0
    · rw [formInner_eq_zero_of_left_eq_zero g.form _ U x hx,
        formInner_eq_zero_of_left_eq_zero g.form _ V x hx]
    · have hs := (ddForm_support _ hξA).trans (multiplyRealForm_support_subset_scalar ξ A)
      have hηx := (hηone x (hs (subset_closure hx))).self_of_nhds
      exact formInner_congr_at g.form rfl (by simp only [V,multiplyRealForm,hηx,one_smul])
  have hPf : P (realizeActualForm g μ (scalarForm f) hf) = realizeActualForm g μ (scalarForm f) hf := by
    rw [show P (realizeActualForm g μ (scalarForm f) hf) =
      realizeActualForm g μ (multiplyRealForm ξ (scalarForm f))
        (l2RealForm_multiply_bounded g μ ξ hm 1 zero_le_one hbound _ hf) from
          multiplyHilbert_actual g μ ξ hm 1 zero_le_one hbound _ hf]
    apply realizeActualForm_congr
    funext x
    ext W
    change ξ x * f x = f x
    by_cases hx : f x = 0
    · simp only [hx,mul_zero]
    · rw [(hξone x (subset_tsupport _ hx)).self_of_nhds,one_mul]
  have he : inner ℝ (realizeActualForm g μ (scalarForm f) hf) (q-qV) = 0 := by
    rw [← hPf,multiplyL2FormHilbert_inner_symm,hz,inner_zero_right]
  rw [inner_sub_right,sub_eq_zero] at he
  rw [he]
  change inner ℝ (realizeActualForm g μ (scalarForm f) hf)
    (realizeActualForm g μ (adjointForm g.form V) _) = _
  rw [realizeActualForm_inner]
  simp only [adjointForm,WeakCurrent.formInner_scalar]
  rfl

/-- Heat-current duality for rough compact scalar data and actual smooth heat
representatives. Initial dd data remain a distribution. -/
theorem dd_heat_current_compact (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (hk : IsKahler g)
    (f : M.Carrier → ℝ) (hf : Continuous f) (hcf : HasCompactSupport f)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B)
    (t : ℝ) (ht : 0 < t) (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (U : RealForm M 2) (hU : SmoothRealForm U)
    (huL2 : L2RealForm g.form μ (scalarForm u)) (hUL2 : L2RealForm g.form μ U)
    (huRep : realizeActualForm g μ (scalarForm u) huL2 =
      hodgeHeatHilbert g μ hμ 0 t
        (realizeActualForm g μ (scalarForm f) (continuous_compact_scalar_l2 g μ hμ f hf hcf)))
    (hURep : realizeActualForm g μ U hUL2 = hodgeHeatHilbert g μ hμ 2 t
      (realizeActualForm g μ B (smooth_compactlySupported_l2RealForm g μ hμ B hB hcB)))
    (η : M.Carrier → ℝ) (hη : SmoothFn η) (hcη : HasCompactSupport η)
    (hηone : ∀ x ∈ tsupport f, ∀ᶠ y in 𝓝 x, η y = 1) :
    (∫ x, formInner g.form (ddRealForm u) B x ∂μ) =
      ∫ x, f x * WeakCurrent.ddAdjointScalar g.form (multiplyRealForm η U) x ∂μ := by
  obtain ⟨ξ,hξ,hcξ,hrange,hξone⟩ := exists_cutoff_one_near g hcf
  obtain ⟨η₀,hη₀,hcη₀,_,hη₀one⟩ := exists_cutoff_one_near g hcξ
  have hη₀f : ∀ x ∈ tsupport f, ∀ᶠ y in 𝓝 x, η₀ y = 1 := by
    intro x hx
    apply hη₀one x
    apply subset_tsupport ξ
    change ξ x ≠ 0
    rw [(hξone x hx).self_of_nhds]
    norm_num
  have hbq := ddAdjointGraph_heat g μ hμ hk (ddAdjointGraph_core g μ hμ B hB hcB) t ht.le
  have he := localized_adjoint_pairing g μ hμ _ _ hbq U hU hUL2 hURep f
    (continuous_compact_scalar_l2 g μ hμ f hf hcf) ξ hξ hcξ hrange hξone η₀ hη₀ hcη₀ hη₀one
  calc
    _ = inner ℝ (realizeActualForm g μ (scalarForm u) huL2)
        (realizeActualForm g μ (adjointForm g.form B) (adjointForm_l2 g μ hμ B hB hcB)) := by
      rw [realizeActualForm_inner,WeakCurrent.integral_dd_eq_adjoint g μ hμ u hu B hB hcB]
      simp only [adjointForm,WeakCurrent.formInner_scalar]
      rfl
    _ = inner ℝ (realizeActualForm g μ (scalarForm f) (continuous_compact_scalar_l2 g μ hμ f hf hcf))
        (hodgeHeatHilbert g μ hμ 0 t
          (realizeActualForm g μ (adjointForm g.form B) (adjointForm_l2 g μ hμ B hB hcB))) := by
      rw [huRep]
      exact hodgeHeatHilbert_symmetric g μ hμ 0 t _ _
    _ = ∫ x, f x * WeakCurrent.ddAdjointScalar g.form (multiplyRealForm η₀ U) x ∂μ := he
    _ = _ := integral_congr_ae (Eventually.of_forall
      (current_cutoff_independent g μ hμ f U hU η₀ η hη₀ hη hη₀f hηone))

end Yau.NodeProofs.P06Aux.DDbarHeat
