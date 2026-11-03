import Yau.Proofs.P06HodgeRegularityWeakProducts
import Yau.Proofs.P06HodgeRegularityScalarEnergy
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Uniqueness and commutation for actual weak coordinate derivatives on
arbitrary finite-dimensional real chart spaces. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsLocallyFiniteMeasure ν]

theorem regularity_ae_eq_of_test_integrals {O : Set E} (hO : IsOpen O)
    {f g : E → ℝ} (hf : MemLp f 2 (ν.restrict O)) (hg : MemLp g 2 (ν.restrict O))
    (ht : ∀ φ, regularityTest O φ →
      (∫ z, f z * φ z ∂ν.restrict O) = ∫ z, g z * φ z ∂ν.restrict O) :
    f =ᵐ[ν.restrict O] g := by
  have hlocal : LocallyIntegrableOn (fun z => f z - g z) O ν :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hf.sub hg).locallyIntegrable (by norm_num))
  have hz := hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal
    (fun φ hφ hcφ hφO => by
      have htφ : regularityTest O φ := ⟨hφ, hcφ, hφO⟩
      have hrest : (∫ z, φ z • (f z - g z) ∂ν) =
          ∫ z, φ z • (f z - g z) ∂ν.restrict O := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hzo
        rw [image_eq_zero_of_notMem_tsupport (fun h => hzo (hφO h)), zero_smul]
      rw [hrest]
      have hfun : (fun z => φ z • (f z - g z)) = fun z => f z * φ z - g z * φ z := by
        funext z
        simp only [smul_eq_mul]
        ring
      have hIf : Integrable (fun z => f z * φ z) (ν.restrict O) :=
        hf.integrable_mul (regularityTest_memLp ν htφ)
      have hIg : Integrable (fun z => g z * φ z) (ν.restrict O) :=
        hg.integrable_mul (regularityTest_memLp ν htφ)
      rw [hfun, integral_sub hIf hIg, ht φ htφ, sub_self])
  filter_upwards [(ae_restrict_iff' hO.measurableSet).mpr hz] with z h
  exact sub_eq_zero.mp h

theorem regularityWeakDeriv_unique {O : Set E} (hO : IsOpen O) {e : E} {u f g : E → ℝ}
    (hf : MemLp f 2 (ν.restrict O)) (hg : MemLp g 2 (ν.restrict O))
    (hwf : regularityWeakDeriv ν O e u f) (hwg : regularityWeakDeriv ν O e u g) :
    f =ᵐ[ν.restrict O] g := by
  apply regularity_ae_eq_of_test_integrals ν hO hf hg
  intro φ hφ
  have h := hwf φ hφ
  have h' := hwg φ hφ
  linarith

/-- The weak Hessian is symmetric for every pair of fixed coordinate
directions. The equality is obtained from the true second derivatives of
smooth tests and uniqueness of distributions. -/
theorem regularityWeakDeriv_commute {ι : Type*} [Fintype ι]
    {O : Set E} (hO : IsOpen O) (v : ι → E) {u : E → ℝ}
    {G : E → ι → ℝ} {H : E → ι → ι → ℝ}
    (hG : ∀ i, regularityWeakDeriv ν O (v i) u (fun z => G z i))
    (hH2 : ∀ i j, MemLp (fun z => H z i j) 2 (ν.restrict O))
    (hH : ∀ i j, regularityWeakDeriv ν O (v i) (fun z => G z j) (fun z => H z i j)) :
    ∀ᵐ z ∂ν.restrict O, ∀ i j, H z i j = H z j i := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  apply regularity_ae_eq_of_test_integrals ν hO (hH2 i j) (hH2 j i)
  intro φ hφ
  have h1 := hH i j φ hφ
  have h2 := hH j i φ hφ
  have h3 := hG j (fun z => fderiv ℝ φ z (v i)) (regularityTest_direction hφ (v i))
  have h4 := hG i (fun z => fderiv ℝ φ z (v j)) (regularityTest_direction hφ (v j))
  have hcomm : (fun z => u z * fderiv ℝ (fun y => fderiv ℝ φ y (v i)) z (v j)) =
      fun z => u z * fderiv ℝ (fun y => fderiv ℝ φ y (v j)) z (v i) := by
    funext z
    exact congrArg (u z * ·) (congrFun (regularityDirection_commute hφ.1 (v j) (v i)) z)
  change (∫ z, u z * fderiv ℝ (fun y => fderiv ℝ φ y (v i)) z (v j) ∂ν.restrict O) = _ at h3
  rw [hcomm] at h3
  linarith

end Yau.NodeProofs.P06Aux
