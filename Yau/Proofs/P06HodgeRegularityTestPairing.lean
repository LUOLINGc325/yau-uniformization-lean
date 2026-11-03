import Yau.Proofs.P06HodgeRegularityScalarTranspose
import Yau.Proofs.P06HodgeRegularityForwardRestriction

/-! Integrable pairings with the actual local compact test space. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsLocallyFiniteMeasure ν]

def regularityTestPairing {O : Set E} (u : E → ℝ) (hu : MemLp u 2 (ν.restrict O)) :
    regularityTestSpace O →ₗ[ℝ] ℝ where
  toFun φ := ∫ z, u z * φ.1 z ∂ν.restrict O
  map_add' φ ψ := by
    simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    exact integral_add (hu.integrable_mul (regularityTest_memLp ν φ.2))
      (hu.integrable_mul (regularityTest_memLp ν ψ.2))
  map_smul' c φ := by
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [show ∀ z, u z * (c * φ.1 z) = c * (u z * φ.1 z) by intro z; ring]
    exact integral_const_mul c _

theorem regularityTestPairing_apply {O : Set E} (u : E → ℝ)
    (hu : MemLp u 2 (ν.restrict O)) (φ : regularityTestSpace O) :
    regularityTestPairing ν u hu φ = ∫ z, u z * φ.1 z ∂ν.restrict O := rfl

theorem regularityScalarTranspose_test
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {O : Set E} {φ : E → ℝ} (hφ : regularityTest O φ) (r c : α) :
    regularityTest O (fun z => regularityScalarTranspose v q e1 e0 φ z r c) := by
  classical
  have heq : (fun z => regularityForwardTranspose v (regularityScalarSystemA q) e1 e0 φ z r c) =
      fun z => regularityScalarTranspose v q e1 e0 φ z r c := by
    funext z
    exact regularityForwardTranspose_scalar v q e1 e0 φ z r c
  rw [← heq]
  exact regularityForwardTranspose_test v (regularityScalarSystemA q) e1 e0
    (regularityScalarSystemA_contDiff q hq) he1 he0 hφ r c

theorem regularityForwardWeak_pairing_iff
    {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {O : Set E} (U W : E → α → ℝ) (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O)) :
    regularityForwardWeak ν O v q e1 e0 U W ↔
      ∀ r φ, regularityTest O φ →
        (∑ c, ∫ z, U z c * regularityScalarTranspose v q e1 e0 φ z r c ∂ν.restrict O) =
          ∫ z, W z r * φ z ∂ν.restrict O := by
  classical
  have htest {φ : E → ℝ} (hφ : regularityTest O φ) r c :
      regularityTest O (fun z => regularityScalarTranspose v q e1 e0 φ z r c) := by
    exact regularityScalarTranspose_test v q e1 e0 hq he1 he0 hφ r c
  have heq r φ (hφ : regularityTest O φ) :
      (∫ z, ∑ c, regularityForwardTranspose v (regularityScalarSystemA q) e1 e0 φ z r c * U z c
        ∂ν.restrict O) =
      ∑ c, ∫ z, U z c * regularityScalarTranspose v q e1 e0 φ z r c ∂ν.restrict O := by
    simp_rw [regularityForwardTranspose_scalar, mul_comm (_ : ℝ) (U _ _)]
    exact integral_finset_sum _ (fun c _ => (hU c).integrable_mul (regularityTest_memLp ν (htest hφ r c)))
  constructor
  · intro h r φ hφ
    rw [← heq r φ hφ]
    simpa only [mul_comm (φ _) (W _ _)] using h r φ hφ
  · intro h r φ hφ
    rw [heq r φ hφ]
    simpa only [mul_comm (φ _) (W _ _)] using h r φ hφ

end Yau.NodeProofs.P06Aux
