import Yau.Proofs.C02OpenBilinearJets

/-! The pullback of a real bilinear field has a fixed convolution
majorant, using the actual derivative field on the same open domain. -/

noncomputable section
open Set
open scoped ContDiff
namespace Yau.Blueprint.C02Proof
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance rbp_end_group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance rbp_end_space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance rbp_dual_group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance rbp_dual_space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance rbp_action_group : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance rbp_action_space : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def realBilinearPullback (H : E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℝ] E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (((ContinuousLinearMap.compL ℝ E E ℝ).flip T).comp (H.comp T))

theorem realBilinearPullback_apply
    (H : E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℝ] E) (u v : E) :
    realBilinearPullback H T u v = H (T u) (T v) := rfl

theorem realBilinearPullback_smoothOn
    {O : Set D} {H : D → E →L[ℝ] E →L[ℝ] ℝ} {T : D → E →L[ℝ] E}
    (hH : ContDiffOn ℝ ∞ H O) (hT : ContDiffOn ℝ ∞ T O) :
    ContDiffOn ℝ ∞ (fun z => realBilinearPullback (H z) (T z)) O := by
  exact (((ContinuousLinearMap.compL ℝ E E ℝ).flip.contDiff.comp_contDiffOn hT).clm_comp
    (hH.clm_comp hT))

theorem norm_realBilinearPullback_jet_le
    {O : Set D} (hO : IsOpen O)
    {H : D → E →L[ℝ] E →L[ℝ] ℝ} {T : D → E →L[ℝ] E}
    (hH : ContDiffOn ℝ ∞ H O) (hT : ContDiffOn ℝ ∞ T O)
    {x : D} (hx : x ∈ O) (m : ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i ≤ m, ‖iteratedFDeriv ℝ i H x‖ ≤ a i)
    (hb : ∀ i ≤ m, ‖iteratedFDeriv ℝ i T x‖ ≤ b i)
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i) :
    ‖iteratedFDeriv ℝ m (fun z => realBilinearPullback (H z) (T z)) x‖ ≤
      binomialJetProduct b (binomialJetProduct a b) m := by
  let L : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ E E ℝ).flip
  let R := fun z => L (T z)
  let P := fun z => (H z).comp (T z)
  have hL : ‖L‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_flip]
    exact ContinuousLinearMap.norm_compL_le ℝ E E ℝ
  have hR : ContDiffOn ℝ ∞ R O := L.contDiff.comp_contDiffOn hT
  have hP : ContDiffOn ℝ ∞ P O := hH.clm_comp hT
  apply norm_iteratedFDeriv_bilinear_on_le
    (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ))
    (ContinuousLinearMap.norm_compL_le ℝ E (E →L[ℝ] ℝ) (E →L[ℝ] ℝ))
    hO hR hP hx m b (binomialJetProduct a b)
  · intro i hi
    exact (norm_iteratedFDeriv_linear_on_le L hL hO hT hx i).trans (hb i hi)
  · intro i hi
    exact norm_iteratedFDeriv_bilinear_on_le
      (ContinuousLinearMap.compL ℝ E E (E →L[ℝ] ℝ))
      (ContinuousLinearMap.norm_compL_le ℝ E E (E →L[ℝ] ℝ))
      hO hH hT hx i a b (fun j hj => ha j (hj.trans hi))
      (fun j hj => hb j (hj.trans hi)) ha0 hb0
  · exact hb0
  · exact binomialJetProduct_nonneg ha0 hb0

end Yau.Blueprint.C02Proof
