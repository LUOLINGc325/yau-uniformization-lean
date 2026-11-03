import Yau.Proofs.P06HodgeRegularityTestPairing
import Yau.LeafProofs.L03DivergenceEnergy

/-! Classical compact-test duality for the actual forward operator.
This is used on independently chosen smooth core approximants only. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [Fintype α]
    (ν : Measure E) [ν.IsAddHaarMeasure]

theorem regularitySmoothTranspose_first
    (u ψ : E → ℝ) (hu : ContDiff ℝ ∞ u) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (e : E) :
    (∫ z, u z * regularityDirection e ψ z ∂ν) =
      -(∫ z, ψ z * regularityDirection e u z ∂ν) := by
  have hi := DivergenceEnergy.compact_ibp ν ψ u hψ hcψ hu e
  have heq : (∫ z, u z * regularityDirection e ψ z ∂ν) =
      ∫ z, regularityDirection e ψ z * u z ∂ν :=
    integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [heq]
  change (∫ z, fderiv ℝ ψ z e * u z ∂ν) = -(∫ z, ψ z * fderiv ℝ u z e ∂ν)
  linarith

theorem regularitySmoothTranspose_second
    (u ψ : E → ℝ) (hu : ContDiff ℝ ∞ u) (hψ : ContDiff ℝ ∞ ψ)
    (hcψ : HasCompactSupport ψ) (e f : E) :
    (∫ z, u z * regularityDirection f (regularityDirection e ψ) z ∂ν) =
      ∫ z, ψ z * regularityDirection e (regularityDirection f u) z ∂ν := by
  have h1 := regularitySmoothTranspose_first ν u (regularityDirection e ψ) hu
    (regularityDirection_contDiff hψ e) (hcψ.fderiv_apply ℝ e) f
  have h2 := regularitySmoothTranspose_first ν (regularityDirection f u) ψ
    (regularityDirection_contDiff hu f) hψ hcψ e
  have heq : (∫ z, regularityDirection e ψ z * regularityDirection f u z ∂ν) =
      ∫ z, regularityDirection f u z * regularityDirection e ψ z ∂ν :=
    integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
  rw [heq] at h1
  linarith

theorem regularitySmoothTranspose_row
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    (u : E → ℝ) (hu : ContDiff ℝ ∞ u) (huL : MemLp u 2 ν)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) (r c : α) :
    (∫ z, u z * regularityForwardTranspose v a e1 e0 φ z r c ∂ν) =
      -(∑ i, ∑ j, ∫ z, (a r c i j z * φ z) *
        regularityDirection (v i) (regularityDirection (v j) u) z ∂ν) +
      (∑ i, ∫ z, (e1 r c i z * φ z) * regularityDirection (v i) u z ∂ν) +
        ∫ z, u z * (e0 r c z * φ z) ∂ν := by
  classical
  have htφ : regularityTest Set.univ φ := ⟨hφ,hcφ,Set.subset_univ _⟩
  let P (i j : ι) : regularityTestSpace (Set.univ : Set E) :=
    ⟨regularityDirection (v j) (regularityDirection (v i) (fun z => a r c i j z * φ z)),
      regularityTest_direction (regularityTest_direction (regularityTest_coeff_mul htφ (ha r c i j)) (v i)) (v j)⟩
  let Q (i : ι) : regularityTestSpace (Set.univ : Set E) :=
    ⟨regularityDirection (v i) (fun z => e1 r c i z * φ z),
      regularityTest_direction (regularityTest_coeff_mul htφ (he1 r c i)) (v i)⟩
  let Z : regularityTestSpace (Set.univ : Set E) :=
    ⟨fun z => e0 r c z * φ z, regularityTest_coeff_mul htφ (he0 r c)⟩
  let T : regularityTestSpace (Set.univ : Set E) :=
    ⟨fun z => regularityForwardTranspose v a e1 e0 φ z r c,
      regularityForwardTranspose_test v a e1 e0 ha he1 he0 htφ r c⟩
  have htest : T = -(∑ i, ∑ j, P i j) - (∑ i, Q i) + Z := by
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_sum,
      Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Finset.sum_apply]
    rfl
  let L := regularityTestPairing ν (O := Set.univ) u (by simpa only [Measure.restrict_univ] using huL)
  have heval := congrArg L htest
  simp only [map_add, map_sub, map_neg, map_sum] at heval
  have hP i j : L (P i j) = ∫ z, (a r c i j z * φ z) *
      regularityDirection (v i) (regularityDirection (v j) u) z ∂ν := by
    change (∫ z, u z * regularityDirection (v j)
      (regularityDirection (v i) (fun y => a r c i j y * φ y)) z ∂ν.restrict Set.univ) = _
    simp only [Measure.restrict_univ]
    exact regularitySmoothTranspose_second ν u _ hu ((ha r c i j).mul hφ) hcφ.mul_left (v i) (v j)
  have hQ i : L (Q i) = -(∫ z, (e1 r c i z * φ z) * regularityDirection (v i) u z ∂ν) := by
    change (∫ z, u z * regularityDirection (v i) (fun y => e1 r c i y * φ y) z ∂ν.restrict Set.univ) = _
    simp only [Measure.restrict_univ]
    exact regularitySmoothTranspose_first ν u _ hu ((he1 r c i).mul hφ) hcφ.mul_left (v i)
  simp_rw [hP,hQ,Finset.sum_neg_distrib] at heval
  simpa only [L,T,Z,regularityTestPairing, LinearMap.coe_mk, AddHom.coe_mk,
    Measure.restrict_univ, sub_neg_eq_add] using heval

end Yau.NodeProofs.P06Aux
