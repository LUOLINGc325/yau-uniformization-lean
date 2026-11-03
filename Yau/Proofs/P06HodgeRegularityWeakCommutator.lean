import Yau.Proofs.P06HodgeRegularityCommutator
import Yau.Proofs.P06HodgeRegularityTestPairing

/-! The transposed-test identity paired with genuinely rough L² fields.
No classical derivative of a rough representative occurs. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α]
    (ν : Measure E) [IsLocallyFiniteMeasure ν]

theorem regularityWeakTranspose_commutator
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i))
    (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {O : Set E} (u : E → ℝ) (G : ι → E → ℝ)
    (hu : MemLp u 2 (ν.restrict O)) (hG : ∀ j, MemLp (G j) 2 (ν.restrict O))
    (hd : ∀ j, regularityWeakDeriv ν O (v j) u (G j))
    {φ : E → ℝ} (hφ : regularityTest O φ) (ell : ι) (r c : α) :
    (∫ z, u z * regularityProlongH v e0 φ ell r c z ∂ν.restrict O) +
      (∫ z, G ell z * regularityScalarTranspose v q e1 e0 φ z r c ∂ν.restrict O) +
      (∑ j, ∫ z, G j z * regularityProlongK v q e1 φ ell r c j z ∂ν.restrict O) =
    -(∫ z, u z * regularityScalarTranspose v q e1 e0
      (regularityDirection (v ell) φ) z r c ∂ν.restrict O) := by
  let T : regularityTestSpace O :=
    ⟨fun z => regularityScalarTranspose v q e1 e0 φ z r c,
      regularityScalarTranspose_test v q e1 e0 hq he1 he0 hφ r c⟩
  let K (j : ι) : regularityTestSpace O :=
    ⟨regularityProlongK v q e1 φ ell r c j, regularityProlongK_test v q e1 hq he1 hφ ell r c j⟩
  let H : regularityTestSpace O :=
    ⟨regularityProlongH v e0 φ ell r c, regularityProlongH_test v e0 he0 hφ ell r c⟩
  let Td : regularityTestSpace O :=
    ⟨fun z => regularityScalarTranspose v q e1 e0 (regularityDirection (v ell) φ) z r c,
      regularityScalarTranspose_test v q e1 e0 hq he1 he0
        (regularityTest_direction hφ (v ell)) r c⟩
  let L := regularityTestPairing ν u hu
  let LG (j : ι) := regularityTestPairing ν (G j) (hG j)
  have hweak (j : ι) (ψ : regularityTestSpace O) :
      L (regularityTestDeriv O (v j) ψ) = -LG j ψ := hd j ψ.1 ψ.2
  have htest : H - regularityTestDeriv O (v ell) T -
      (∑ j, regularityTestDeriv O (v j) (K j)) = -Td := by
    apply Subtype.ext
    funext z
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_neg,
      Pi.sub_apply, Pi.neg_apply, Finset.sum_apply]
    dsimp only [H, T, K, Td, regularityTestDeriv, LinearMap.coe_mk, AddHom.coe_mk]
    change regularityProlongH v e0 φ ell r c z -
      regularityDirection (v ell) (fun y => regularityScalarTranspose v q e1 e0 φ y r c) z -
      (∑ j, regularityDirection (v j) (regularityProlongK v q e1 φ ell r c j) z) = _
    exact regularityTranspose_commutator v q e1 e0 hq he1 he0 hφ.1 ell r c z
  have hp := congrArg L htest
  simp only [map_sub, map_sum, map_neg, hweak, Finset.sum_neg_distrib] at hp
  change L H + LG ell T + (∑ j, LG j (K j)) = -L Td
  linarith

end Yau.NodeProofs.P06Aux
