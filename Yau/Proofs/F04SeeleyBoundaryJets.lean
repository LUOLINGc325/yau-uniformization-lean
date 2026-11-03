import Yau.Proofs.F04SeeleyCutoff
import Yau.Proofs.F04SeeleyTensorMoments

open Filter Set
open scoped Topology ContDiff

noncomputable section

namespace Yau.F04Proof.Seeley

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
theorem positiveCutoff_one_germ {χ : ℝ → ℝ} {δ : ℝ} {f : E × ℝ → F}
    (hδ : 0 < δ) (hχone : ∀ s : ℝ, |s| ≤ δ / 2 → χ s = 1) (x : E) :
    positiveCutoff χ f =ᶠ[𝓝 (x, 0)] f := by
  have hn : {p : E × ℝ | p.2 ∈ Ioo (-δ / 2) (δ / 2)} ∈ 𝓝 (x, 0) :=
    continuous_snd.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hn] with p hp
  change χ p.2 • f p = f p
  rw [hχone p.2 (abs_le.mpr ⟨by linarith [hp.1], hp.2.le⟩), one_smul]

theorem positiveCutoff_jet_at_zero {O : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hδ : 0 < δ) (hS : 0 < S) (hχone : ∀ s : ℝ, |s| ≤ δ / 2 → χ s = 1)
    (m : ℕ) (x : E) :
    iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0) (x, 0) =
      iteratedFDerivWithin ℝ m f (O ×ˢ Icc 0 S) (x, 0) := by
  have he := positiveCutoff_one_germ (f := f) hδ hχone x
  have hs : (O ×ˢ Ici (0 : ℝ)) =ᶠ[𝓝 (x, 0)] (O ×ˢ Icc 0 S) := by
    have hn : {p : E × ℝ | p.2 < S} ∈ 𝓝 (x, 0) :=
      continuous_snd.continuousAt.preimage_mem_nhds (Iio_mem_nhds hS)
    filter_upwards [hn] with p hp
    apply propext
    simp only [mem_prod, mem_Ici, mem_Icc, and_iff_left hp.le]
  rw [(he.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq he.eq_of_nhds m]
  exact iteratedFDerivWithin_congr_set hs m

def negativeJet (O : Set E) (χ : ℝ → ℝ) (f : E × ℝ → F) (m : ℕ) (p : E × ℝ) : Jet E F m :=
  ∑' k, seeleyWeight k •
    (iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0) (reflectLinear k p)).compContinuousLinearMap
      (fun _ : Fin m => reflectLinear k)

def seeleyExtend (χ : ℝ → ℝ) (f : E × ℝ → F) : E × ℝ → F := fun p =>
  if p.2 < 0 then ∑' k, seeleyWeight k • positiveCutoff χ f (reflectLinear k p) else f p

theorem seeleyExtend_eq_nonneg (χ : ℝ → ℝ) (f : E × ℝ → F) (p : E × ℝ) (hp : 0 ≤ p.2) :
    seeleyExtend χ f p = f p := by
  simp only [seeleyExtend, not_lt.mpr hp, ite_false]

variable [CompleteSpace F]

theorem negativeJet_at_zero {O : Set E} {S δ : ℝ} {χ : ℝ → ℝ} {f : E × ℝ → F}
    (hδ : 0 < δ) (hS : 0 < S) (hχone : ∀ s : ℝ, |s| ≤ δ / 2 → χ s = 1)
    (m : ℕ) (x : E) :
    negativeJet O χ f m (x, 0) = iteratedFDerivWithin ℝ m f (O ×ˢ Icc 0 S) (x, 0) := by
  unfold negativeJet
  simp only [reflectLinear_apply, mul_zero]
  rw [(seeley_tensor_moment m
    (iteratedFDerivWithin ℝ m (positiveCutoff χ f) (O ×ˢ Ici 0) (x, 0))).tsum_eq]
  exact positiveCutoff_jet_at_zero hδ hS hχone m x

end Yau.F04Proof.Seeley
