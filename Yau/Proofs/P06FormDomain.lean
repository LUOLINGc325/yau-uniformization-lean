import Yau.LeafProofs.L03Complete

/-! The original prequotient form domain: weak derivative uniqueness and the
actual compact smooth core.  All distances and pairings below are those in
the frozen Hodge contracts. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ENNReal

namespace Yau.NodeProofs.P06Aux
open Yau Yau.Blueprint Yau.LeafProofs.L03

variable {n k : ℕ} {M : ComplexManifold n}

theorem representsExterior_unique {A : RealForm M k} {B C : RealForm M (k + 1)}
    (hB : RepresentsExterior A B) (hC : RepresentsExterior A C) : B = C := by
  apply realForm_eq_of_center_components
  intro x I
  exact (hB x (chartPt x x) (mem_extChartAt_target x) I).trans
    (hC x (chartPt x x) (mem_extChartAt_target x) I).symm

/-- Every graph-closure witness can be expressed using the genuine computed
exterior derivative and codifferential of its compact smooth approximants. -/
theorem formGraph_sequence (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A : RealForm M 2}
    {dA : RealForm M 3} {δA : RealForm M 1}
    (h : HodgeFormGraphClosure g.form μ A dA δA) :
    ∃ As : ℕ → RealForm M 2,
      (∀ j, SmoothRealForm (As j) ∧ CompactlySupportedRealForm (As j)) ∧
      Tendsto (fun j => formL2DistanceSq g.form μ (As j) A) atTop (𝓝 0) ∧
      Tendsto (fun j => formL2DistanceSq g.form μ (exteriorRealForm (As j)) dA) atTop (𝓝 0) ∧
      Tendsto (fun j => formL2DistanceSq g.form μ (codifferentialRealForm g.form (As j)) δA)
        atTop (𝓝 0) := by
  obtain ⟨_hA, _hdA, _hδA, As, ds, δs, hc, ht⟩ := h
  have hs (j : ℕ) : SmoothRealForm (As j) ∧ CompactlySupportedRealForm (As j) :=
    ⟨(hc j).1, (hc j).2.1⟩
  have hd (j : ℕ) : ds j = exteriorRealForm (As j) := by
    obtain ⟨hAs, _hcAs, _hds, hds, _hδs, _hδrep, _hAL, _hdL, _hδL⟩ := hc j
    exact representsExterior_unique hds (exteriorRealForm_represents _ hAs)
  have hδ (j : ℕ) : δs j = codifferentialRealForm g.form (As j) := by
    obtain ⟨hAs, _hcAs, _hds, _hdsrep, _hδs, hδrep, _hAL, _hdL, _hδL⟩ := hc j
    exact representsCodifferential_unique g.form hδrep
      (codifferentialRealForm_represents g μ hμ _ hAs)
  simp_rw [hd, hδ] at ht
  refine ⟨As, hs, ?_, ?_, ?_⟩
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro j
    exact (le_add_of_nonneg_right (by positivity)).trans
      (le_add_of_nonneg_right (by positivity))
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro j
    exact (le_add_of_nonneg_left (by positivity)).trans
      (le_add_of_nonneg_right (by positivity))
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    exact fun _ => le_add_of_nonneg_left (by positivity)

/-- Actual compact smooth tests separate all L² forms in every degree. -/
theorem l2Form_ae_eq_of_compact_pairings (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (W Z : RealForm M k)
    (hW : L2RealForm g.form μ W) (hZ : L2RealForm g.form μ Z)
    (hp : ∀ B : RealForm M k, SmoothRealForm B → CompactlySupportedRealForm B →
      (∫ y, formInner g.form W B y ∂μ) = ∫ y, formInner g.form Z B y ∂μ) :
    ∀ᵐ y ∂μ, W y = Z y := by
  let w := L2FormSpace.ofSection W hW
  let z := L2FormSpace.ofSection Z hZ
  have hs : closure (Prod.fst '' hodgeCoreRealizedGraph g μ k) ⊆
      {v : L2FormHilbert g μ k | inner ℝ (realizeL2Form g μ w) v =
        inner ℝ (realizeL2Form g μ z) v} := by
    apply closure_minimal
    · rintro v ⟨p, hp', rfl⟩
      obtain ⟨B, C, hBC, rfl⟩ := hp'
      simpa only [Set.mem_ofPred_eq, Prod.fst, Prod.snd, realizeL2Form_inner,
        w, z, L2FormSpace.toSection_ofSection] using hp B hBC.1 hBC.2.1
    · exact isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
  have heq : realizeL2Form g μ w = realizeL2Form g μ z := by
    apply ext_inner_right ℝ
    intro v
    apply hs
    rw [(hodgeCoreRealizedGraph_domain_dense g μ hμ k).closure_eq]
    trivial
  exact (realizeL2Form_eq_iff_ae g μ w z).mp heq

/-- Graph closure retains the exterior weak derivative against every actual
compact smooth test; there is no chosen distributional operator. -/
theorem formGraph_exterior_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A : RealForm M 2}
    {dA : RealForm M 3} {δA : RealForm M 1}
    (h : HodgeFormGraphClosure g.form μ A dA δA)
    (B : RealForm M 3) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ y, formInner g.form dA B y ∂μ) =
      ∫ y, formInner g.form A (codifferentialRealForm g.form B) y ∂μ := by
  obtain ⟨As, hs, htA, htd, _htδ⟩ := formGraph_sequence g μ hμ h
  have hAL (j : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _ (hs j).1 (hs j).2
  have hdL (j : ℕ) := exteriorRealForm_l2 g μ hμ _ (hs j).1 (hs j).2
  have hBL := smooth_compactlySupported_l2RealForm g μ hμ B hB hcB
  have hδBL := codifferentialRealForm_l2 g μ hμ B hB hcB
  have hd := formL2DistanceSq_tendsto_integral_pairing g μ _ dA B hdL h.2.1 hBL htd
  have ha := formL2DistanceSq_tendsto_integral_pairing g μ As A _ hAL h.1 hδBL htA
  have he (j : ℕ) := integral_exterior_codifferential g μ hμ (As j) B (hs j).1 hB (hs j).2
  exact tendsto_nhds_unique hd (ha.congr' (Eventually.of_forall fun j => (he j).symm))

/-- The same closure retains the true codifferential weak derivative. -/
theorem formGraph_codifferential_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A : RealForm M 2}
    {dA : RealForm M 3} {δA : RealForm M 1}
    (h : HodgeFormGraphClosure g.form μ A dA δA)
    (B : RealForm M 1) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ y, formInner g.form δA B y ∂μ) =
      ∫ y, formInner g.form A (exteriorRealForm B) y ∂μ := by
  obtain ⟨As, hs, htA, _htd, htδ⟩ := formGraph_sequence g μ hμ h
  have hAL (j : ℕ) := smooth_compactlySupported_l2RealForm g μ hμ _ (hs j).1 (hs j).2
  have hδL (j : ℕ) := codifferentialRealForm_l2 g μ hμ _ (hs j).1 (hs j).2
  have hBL := smooth_compactlySupported_l2RealForm g μ hμ B hB hcB
  have hdBL := exteriorRealForm_l2 g μ hμ B hB hcB
  have hd := formL2DistanceSq_tendsto_integral_pairing g μ _ δA B hδL h.2.2.1 hBL htδ
  have ha := formL2DistanceSq_tendsto_integral_pairing g μ As A _ hAL h.1 hdBL htA
  have he (j : ℕ) :
      (∫ y, formInner g.form (codifferentialRealForm g.form (As j)) B y ∂μ) =
        ∫ y, formInner g.form (As j) (exteriorRealForm B) y ∂μ := by
    rw [formInner_symm g.form (codifferentialRealForm g.form (As j)) B,
      formInner_symm g.form (As j) (exteriorRealForm B)]
    exact (integral_exterior_codifferential g μ hμ B (As j) hB (hs j).1 hcB).symm
  exact tendsto_nhds_unique hd (ha.congr' (Eventually.of_forall fun j => (he j).symm))

/-- The first original form-domain conclusion: both weak derivatives are
single valued modulo the actual Riemannian a.e. relation. -/
theorem formGraph_unique (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (dA dB : RealForm M 3) (δA δB : RealForm M 1)
    (hA : HodgeFormGraphClosure g.form μ A dA δA)
    (hB : HodgeFormGraphClosure g.form μ A dB δB) :
    (∀ᵐ y ∂μ, dA y = dB y) ∧ (∀ᵐ y ∂μ, δA y = δB y) := by
  constructor
  · apply l2Form_ae_eq_of_compact_pairings g μ hμ dA dB hA.2.1 hB.2.1
    intro B hs hc
    exact (formGraph_exterior_pairing g μ hμ hA B hs hc).trans
      (formGraph_exterior_pairing g μ hμ hB B hs hc).symm
  · apply l2Form_ae_eq_of_compact_pairings g μ hμ δA δB hA.2.2.1 hB.2.2.1
    intro B hs hc
    exact (formGraph_codifferential_pairing g μ hμ hA B hs hc).trans
      (formGraph_codifferential_pairing g μ hμ hB B hs hc).symm

/-- The original compact core lies in the exact first-order graph closure. -/
theorem formGraph_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    HodgeFormGraphClosure g.form μ A (exteriorRealForm A)
      (codifferentialRealForm g.form A) := by
  have hAL := smooth_compactlySupported_l2RealForm g μ hμ A hA hcA
  have hdL := exteriorRealForm_l2 g μ hμ A hA hcA
  have hδL := codifferentialRealForm_l2 g μ hμ A hA hcA
  refine ⟨hAL, hdL, hδL, (fun _ => A), (fun _ => exteriorRealForm A),
    (fun _ => codifferentialRealForm g.form A), ?_, ?_⟩
  · intro j
    exact ⟨hA, hcA, exteriorRealForm_smooth A hA, exteriorRealForm_represents A hA,
      codifferentialRealForm_smooth g μ hμ A hA, codifferentialRealForm_represents g μ hμ A hA,
      hAL, hdL, hδL⟩
  · simpa only [formL2DistanceSq_self, zero_add] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- The second original form-domain conclusion: its variational Hodge
relation has a unique actual L² output. -/
theorem friedrichsHodge_unique (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W Z : RealForm M 2)
    (hW : FriedrichsHodgeRelation g.form μ A W)
    (hZ : FriedrichsHodgeRelation g.form μ A Z) : ∀ᵐ y ∂μ, W y = Z y := by
  obtain ⟨_hWL, dA, δA, hA, hvarW⟩ := hW
  obtain ⟨_hZL, dB, δB, hB, hvarZ⟩ := hZ
  obtain ⟨hd, hδ⟩ := formGraph_unique g μ hμ A dA dB δA δB hA hB
  apply l2Form_ae_eq_of_compact_pairings g μ hμ W Z _hWL _hZL
  intro B hs hc
  have ht := formGraph_core g μ hμ B hs hc
  have hw := (hvarW B _ _ ht).2.2.2
  have hz := (hvarZ B _ _ ht).2.2.2
  have hid : formInner g.form dA (exteriorRealForm B) =ᵐ[μ]
      formInner g.form dB (exteriorRealForm B) :=
    formInner_congr_ae g.form hd (Eventually.of_forall fun _ => rfl)
  have hiδ : formInner g.form δA (codifferentialRealForm g.form B) =ᵐ[μ]
      formInner g.form δB (codifferentialRealForm g.form B) :=
    formInner_congr_ae g.form hδ (Eventually.of_forall fun _ => rfl)
  exact hw.symm.trans ((congrArg₂ (· + ·) (integral_congr_ae hid) (integral_congr_ae hiδ)).trans hz)

/-- The first-order graph closure retains the actual second-order Green
identity against every compact smooth form. -/
theorem formGraph_energy_pairing (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) {A : RealForm M 2}
    {dA : RealForm M 3} {δA : RealForm M 1}
    (h : HodgeFormGraphClosure g.form μ A dA δA)
    (B : RealForm M 2) (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ y, formInner g.form dA (exteriorRealForm B) y ∂μ) +
      (∫ y, formInner g.form δA (codifferentialRealForm g.form B) y ∂μ) =
        ∫ y, formInner g.form A (hodgeRealForm g.form 2 B) y ∂μ := by
  obtain ⟨As, hs, htA, htd, htδ⟩ := formGraph_sequence g μ hμ h
  exact hodge_energy_limit_pairing g μ hμ As (fun j => (hs j).1) (fun j => (hs j).2)
    A dA δA h.1 h.2.1 h.2.2.1 htA htd htδ B hB hcB

/-- The frozen variational relation implies the actual maximal weak Hodge
equation, by testing its first-order domain with the compact smooth core. -/
theorem friedrichsHodge_maximal (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M 2)
    (h : FriedrichsHodgeRelation g.form μ A W) :
    OperatorCandidates.HodgeMaximalGraph g.form μ A W := by
  obtain ⟨hWL, dA, δA, hA, hvar⟩ := h
  refine ⟨hA.1, hWL, ?_⟩
  intro B Z hc
  obtain ⟨hB, hcB, rfl⟩ := (hodgeCorePair_iff_computed g μ hμ B Z).mp hc
  have hZL := hodgeRealForm_l2 g μ hμ B hB hcB
  have hBL := smooth_compactlySupported_l2RealForm g μ hμ B hB hcB
  refine ⟨formInner_integrable g μ _ _ hA.1 hZL,
    formInner_integrable g μ _ _ hWL hBL, ?_⟩
  exact (formGraph_energy_pairing g μ hμ hA B hB hcB).symm.trans
    (hvar B _ _ (formGraph_core g μ hμ B hB hcB)).2.2.2

theorem hodgeMaximalGraph_unique (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W Z : RealForm M 2)
    (hW : OperatorCandidates.HodgeMaximalGraph g.form μ A W)
    (hZ : OperatorCandidates.HodgeMaximalGraph g.form μ A Z) :
    ∀ᵐ y ∂μ, W y = Z y := by
  apply l2Form_ae_eq_of_compact_pairings g μ hμ W Z hW.2.1 hZ.2.1
  intro B hs hc
  have ht := hodgeRealForm_corePair g μ hμ B hs hc
  exact ((hW.2.2 B _ ht).2.2).symm.trans ((hZ.2.2 B _ ht).2.2)

/-- The fourth original form-domain conclusion: on the actual compact smooth
core, the variational operator is the computed pointwise Hodge Laplacian. -/
theorem friedrichsHodge_represents (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W : RealForm M 2)
    (hA : SmoothRealForm A) (hW : SmoothRealForm W)
    (hcA : CompactlySupportedRealForm A)
    (h : FriedrichsHodgeRelation g.form μ A W) : RepresentsHodge g.form A W := by
  have hcore := hodgeRealForm_corePair g μ hμ A hA hcA
  have hmax := hodgeMinimalGraph_implies_maximal g μ hμ (hodgeCorePair_minimal hcore)
  have hae := hodgeMaximalGraph_unique g μ hμ A W _ (friedrichsHodge_maximal g μ hμ A W h) hmax
  have heq := smoothRealForm_eq_of_ae g μ hμ W (hodgeRealForm g.form 2 A) hW
    (hodgeRealForm_smooth g μ hμ A hA) hae
  rw [heq]
  exact hodgeRealForm_represents g μ hμ A hA

/-- The fifth original form-domain conclusion, with all test memberships and
integrability produced from the original compact smooth datum. -/
theorem friedrichsHodge_core (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A : RealForm M 2)
    (hA : SmoothRealForm A) (hcA : CompactlySupportedRealForm A) :
    ∃ W, SmoothRealForm W ∧ RepresentsHodge g.form A W ∧
      FriedrichsHodgeRelation g.form μ A W := by
  let W := hodgeRealForm g.form 2 A
  have hWL := hodgeRealForm_l2 g μ hμ A hA hcA
  have hdAL := exteriorRealForm_l2 g μ hμ A hA hcA
  have hδAL := codifferentialRealForm_l2 g μ hμ A hA hcA
  refine ⟨W, hodgeRealForm_smooth g μ hμ A hA,
    hodgeRealForm_represents g μ hμ A hA, hWL, exteriorRealForm A,
    codifferentialRealForm g.form A, formGraph_core g μ hμ A hA hcA, ?_⟩
  intro V dV δV hV
  refine ⟨formInner_integrable g μ _ _ hdAL hV.2.1,
    formInner_integrable g μ _ _ hδAL hV.2.2.1,
    formInner_integrable g μ _ _ hWL hV.1, ?_⟩
  rw [formInner_symm g.form (exteriorRealForm A) dV,
    formInner_symm g.form (codifferentialRealForm g.form A) δV,
    formInner_symm g.form W V]
  exact formGraph_energy_pairing g μ hμ hV A hA hcA

end Yau.NodeProofs.P06Aux
