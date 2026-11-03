import spec.WORKPACKAGES.STATEMENTS.MASS.EnergyBindings

open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.F04Proof
open Yau.MassTargetStatements

theorem setIntegral_time_test_of_subset
    {I J : Set ℝ} (hIJ : I ⊆ J) {η : ℝ → ℝ} (hη : tsupport η ⊆ I) (F : ℝ → ℝ) :
    (∫ t in J, η t * F t) = ∫ t in I, η t * F t := by
  have hI : (∫ t in I, η t * F t) = ∫ t, η t * F t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hη h)),zero_mul]
  have hJ : (∫ t in J, η t * F t) = ∫ t, η t * F t := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hIJ (hη h))),zero_mul]
  exact hJ.trans hI.symm

/-- Restriction of the ORIGINAL variational solution to a shorter time
 horizon is proved with the actual compact-test integrals, including the
 support of the test derivative. No new solver or trace is chosen. -/
theorem variationalSolution_restrict_horizon
    {n : ℕ} {M : ComplexManifold n} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (μ : Measure M.Carrier) (Ω : Set M.Carrier) {S T : ℝ} (hTS : T ≤ S)
    (j : V →L[ℝ] FixedPivot μ Ω) (B : ℝ → V →L[ℝ] EnergyDual V)
    (f : ℝ → FixedPivot μ Ω) (u : ℝ → V) (w : ℝ → EnergyDual V) (A : ℝ → FixedPivot μ Ω)
    (hSol : VariationalSolution μ Ω S j B f u w A) :
    VariationalSolution μ Ω T j B f u w A := by
  have hI : Ioo (0 : ℝ) T ⊆ Ioo 0 S := fun t ht => ⟨ht.1,ht.2.trans_le hTS⟩
  have hm : volume.restrict (Ioo (0 : ℝ) T) ≤ volume.restrict (Ioo 0 S) := Measure.restrict_mono_set _ hI
  rcases hSol with ⟨hu,hw,hAc,hA0,hAU,hScalar,hEq⟩
  refine ⟨hu.mono_measure hm,hw.mono_measure hm,hAc.mono (Icc_subset_Icc le_rfl hTS),hA0,
    ae_restrict_of_ae_restrict_of_subset hI hAU,?_,ae_restrict_of_ae_restrict_of_subset hI hEq⟩
  intro v η hη hcη hsη
  have he := hScalar v η hη hcη (hsη.trans hI)
  rw [setIntegral_time_test_of_subset hI hsη (fun t => w t v),
    setIntegral_time_test_of_subset hI ((tsupport_deriv_subset (f := η)).trans hsη)
      (fun t => inner ℝ (A t) (j v))] at he
  exact he

/-- The same actual nonsymmetric form binding also restricts to the
 shorter horizon; no coefficient/form witness is replaced. -/
theorem intrinsicFormBinding_restrict_horizon
    {n : ℕ} {M : ComplexManifold n} {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (g : HermitianField M) (μ : Measure M.Carrier) (Ω : Set M.Carrier)
    (h : ℝ → HermitianField M) {S T C α shift : ℝ} (hTS : T ≤ S)
    (j : V →L[ℝ] FixedPivot μ Ω) (e : (M.Carrier → ℝ) → RealForm M 1 → V)
    (B : ℝ → V →L[ℝ] EnergyDual V) (hForm : IntrinsicFormBinding g μ Ω h S C α shift j e B) :
    IntrinsicFormBinding g μ Ω h T C α shift j e B := by
  exact ⟨hForm.1,hForm.2.1,hForm.2.2.1,hForm.2.2.2.1,
    fun t ht => hForm.2.2.2.2 t ⟨ht.1,ht.2.trans hTS⟩⟩

end Yau.F04Proof
