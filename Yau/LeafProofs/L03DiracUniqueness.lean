import Yau.LeafProofs.L03DiracLinear

open MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

namespace Yau.LeafProofs.L03

variable {n : ℕ} {M : ComplexManifold n}

/-- A genuine graded section concentrated in one actual form degree. -/
def gradedSingleForm (k : ℕ) (B : RealForm M k) : OperatorCandidates.GradedRealForm M :=
  Pi.single k B

theorem gradedSingleForm_smooth_compact {k : ℕ} (B : RealForm M k)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    ∀ j, SmoothRealForm (gradedSingleForm k B j) ∧ CompactlySupportedRealForm (gradedSingleForm k B j) := by
  intro j
  by_cases hj : j = k
  · subst j
    simpa only [gradedSingleForm, Pi.single_eq_same] using And.intro hB hcB
  · simp only [gradedSingleForm, Pi.single_eq_of_ne hj]
    exact ⟨smoothRealForm_zero, by simp [CompactlySupportedRealForm]⟩

/-- Single-degree tests read exactly the actual degreewise metric pairing
in every degree retained by the original finite exterior algebra. -/
theorem gradedInner_single_right (g : HermitianField M) (A : OperatorCandidates.GradedRealForm M)
    (k : ℕ) (B : RealForm M k) (hk : k ≤ 2 * n) :
    OperatorCandidates.gradedInner g A (gradedSingleForm k B) = formInner g (A k) B := by
  classical
  funext y
  let i : Fin (2 * n + 1) := ⟨k, by omega⟩
  unfold OperatorCandidates.gradedInner
  rw [Finset.sum_eq_single i]
  · simp only [i, gradedSingleForm, Pi.single_eq_same]
  · intro j _ hji
    have hj : j.val ≠ k := by
      intro h
      apply hji
      exact Fin.ext h
    simp only [gradedSingleForm, Pi.single_eq_of_ne hj, formInner_zero_right, Pi.zero_apply]
  · simp

/-- Any two outputs of the original maximal graph agree against every
actual compact smooth test form, degree by degree. -/
theorem diracMaximalGraph_output_pairing_eq (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W Z : OperatorCandidates.GradedRealForm M)
    (hAW : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (hAZ : OperatorCandidates.DiracMaximalGraph g.form μ A Z)
    (k : ℕ) (B : RealForm M k) (hk : k ≤ 2 * n)
    (hB : SmoothRealForm B) (hcB : CompactlySupportedRealForm B) :
    (∫ y, formInner g.form (W k) B y ∂μ) = ∫ y, formInner g.form (Z k) B y ∂μ := by
  let C := gradedSingleForm k B
  have hC := gradedSingleForm_smooth_compact B hB hcB
  have hc := diracRealForm_corePair g μ hμ C (fun j => (hC j).1) (fun j => (hC j).2)
  have hw := (hAW.2.2 C (diracRealForm g.form C) hc).2.2
  have hz := (hAZ.2.2 C (diracRealForm g.form C) hc).2.2
  have heq := hw.symm.trans hz
  simpa only [C, gradedInner_single_right g.form W k B hk, gradedInner_single_right g.form Z k B hk] using heq

/-- The actual maximal Dirac graph is single valued modulo the exact
Riemannian a.e. relation. Density is supplied by the proved genuine compact
smooth core, with no extra density hypothesis. -/
theorem diracMaximalGraph_output_ae_unique (g : SmoothMetric M) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (A W Z : OperatorCandidates.GradedRealForm M)
    (hAW : OperatorCandidates.DiracMaximalGraph g.form μ A W)
    (hAZ : OperatorCandidates.DiracMaximalGraph g.form μ A Z) :
    ∀ k, ∀ᵐ y ∂μ, W k y = Z k y := by
  intro k
  by_cases hk : k ≤ 2 * n
  · let w := L2FormSpace.ofSection (W k) (hAW.2.1.2 k)
    let z := L2FormSpace.ofSection (Z k) (hAZ.2.1.2 k)
    have hs : closure (Prod.fst '' hodgeCoreRealizedGraph g μ k) ⊆
        {v : L2FormHilbert g μ k | inner ℝ (realizeL2Form g μ w) v = inner ℝ (realizeL2Form g μ z) v} := by
      apply closure_minimal
      · rintro v ⟨p, hp, rfl⟩
        obtain ⟨B, C, hBC, rfl⟩ := hp
        simpa only [Set.mem_setOf_eq, Prod.fst, Prod.snd, realizeL2Form_inner, w, z, L2FormSpace.toSection_ofSection] using
          diracMaximalGraph_output_pairing_eq g μ hμ A W Z hAW hAZ k B hk hBC.1 hBC.2.1
      · exact isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    have heq : realizeL2Form g μ w = realizeL2Form g μ z := by
      apply ext_inner_right ℝ
      intro v
      apply hs
      rw [(hodgeCoreRealizedGraph_domain_dense g μ hμ k).closure_eq]
      trivial
    exact (realizeL2Form_eq_iff_ae g μ w z).mp heq
  · have hgt : 2 * n < k := Nat.lt_of_not_ge hk
    exact Filter.Eventually.of_forall fun y => by
      rw [hAW.2.1.1 k hgt, hAZ.2.1.1 k hgt]

end Yau.LeafProofs.L03
