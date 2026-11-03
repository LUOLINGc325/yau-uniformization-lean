import Yau.Proofs.P06HodgeRegularityForwardWeak
import Yau.Proofs.P06HodgeRegularityWeakProducts

/-! Supported forward PDE tests restrict to smaller regions. Restricting
a Haar measure is never substituted for the local test quantifier. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype α]

theorem regularityScalarSystemA_contDiff [DecidableEq α] (q : ι → ι → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j)) (r c : α) (i j : ι) :
    ContDiff ℝ ∞ (regularityScalarSystemA q r c i j) := by
  unfold regularityScalarSystemA
  by_cases h : r = c
  · simpa only [h, ite_true] using hq i j
  · simp only [h, ite_false]
    exact contDiff_const

theorem regularityForwardTranspose_integral_restrict
    (ν : Measure E) (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {O : Set E} {φ : E → ℝ} (hφ : regularityTest O φ) (U : E → α → ℝ) (r : α) :
    (∫ z, ∑ c, regularityForwardTranspose v a e1 e0 φ z r c * U z c ∂ν.restrict O) =
      ∫ z, ∑ c, regularityForwardTranspose v a e1 e0 φ z r c * U z c ∂ν := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hzo
  apply Finset.sum_eq_zero
  intro c _
  have ht := regularityForwardTranspose_test v a e1 e0 ha he1 he0 hφ r c
  rw [image_eq_zero_of_notMem_tsupport (fun h => hzo (ht.2.2 h)), zero_mul]

theorem regularityForwardSource_integral_restrict (ν : Measure E)
    {O : Set E} {φ : E → ℝ} (hφ : regularityTest O φ) (w : E → ℝ) :
    (∫ z, φ z * w z ∂ν.restrict O) = ∫ z, φ z * w z ∂ν := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hzo
  rw [image_eq_zero_of_notMem_tsupport (fun h => hzo (hφ.2.2 h)), zero_mul]

theorem regularityForwardWeak_mono [DecidableEq α]
    (ν : Measure E) (v : ι → E) (q : ι → ι → E → ℝ)
    (e1 : α → α → ι → E → ℝ) (e0 : α → α → E → ℝ)
    (hq : ∀ i j, ContDiff ℝ ∞ (q i j))
    (he1 : ∀ r c i, ContDiff ℝ ∞ (e1 r c i)) (he0 : ∀ r c, ContDiff ℝ ∞ (e0 r c))
    {O V : Set E} {U W : E → α → ℝ}
    (h : regularityForwardWeak ν O v q e1 e0 U W) (hVO : V ⊆ O) :
    regularityForwardWeak ν V v q e1 e0 U W := by
  intro r φ hφ
  have hφO : regularityTest O φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVO⟩
  have hh := h r φ hφO
  have ha := regularityScalarSystemA_contDiff (α := α) q hq
  rw [regularityForwardTranspose_integral_restrict ν v _ e1 e0 ha he1 he0 hφO U r,
    regularityForwardSource_integral_restrict ν hφO (fun z => W z r)] at hh
  rw [regularityForwardTranspose_integral_restrict ν v _ e1 e0 ha he1 he0 hφ U r,
    regularityForwardSource_integral_restrict ν hφ (fun z => W z r)]
  exact hh

theorem regularityForwardWeak_congr_on [DecidableEq α]
    (ν : Measure E) {O : Set E} (hO : IsOpen O)
    {v : ι → E} {q : ι → ι → E → ℝ}
    {e1 : α → α → ι → E → ℝ} {e0 : α → α → E → ℝ}
    {U W U' W' : E → α → ℝ}
    (h : regularityForwardWeak ν O v q e1 e0 U W)
    (hU : ∀ z ∈ O, ∀ c, U' z c = U z c) (hW : ∀ z ∈ O, ∀ c, W' z c = W z c) :
    regularityForwardWeak ν O v q e1 e0 U' W' := by
  intro r φ hφ
  calc
    _ = ∫ z, ∑ c, regularityForwardTranspose v (regularityScalarSystemA q) e1 e0 φ z r c * U z c
        ∂ν.restrict O := by
      apply setIntegral_congr_fun hO.measurableSet
      intro z hz
      dsimp only
      apply Finset.sum_congr rfl
      intro c _
      rw [hU z hz c]
    _ = ∫ z, φ z * W z r ∂ν.restrict O := h r φ hφ
    _ = _ := by
      apply setIntegral_congr_fun hO.measurableSet
      intro z hz
      dsimp only
      rw [hW z hz r]

theorem regularityWeakDeriv_congr_on (ν : Measure E) [IsLocallyFiniteMeasure ν]
    {O : Set E} (hO : IsOpen O) {e : E} {u du u' du' : E → ℝ}
    (h : regularityWeakDeriv ν O e u du)
    (hu : ∀ z ∈ O, u z = u' z) (hd : ∀ z ∈ O, du z = du' z) :
    regularityWeakDeriv ν O e u' du' := by
  apply regularityWeakDeriv_congr_ae ν h
  · filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    exact hu z hz
  · filter_upwards [ae_restrict_mem hO.measurableSet] with z hz
    exact hd z hz

end Yau.NodeProofs.P06Aux
