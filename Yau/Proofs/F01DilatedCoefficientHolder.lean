import Yau.Proofs.F01UniformFirstJetBudget

/-! Uniform genuine first jets supply the parabolic coefficient budget
before every chart, spatial dilation and bounded affine time coefficient. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dilated_affine_holder_budget {f g : ι → Space n → F} {r β : ℝ}
    (hf : UniformJetBounds 1 f (fun _ => ball 0 r))
    (hg : UniformJetBounds 1 g (fun _ => ball 0 r))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 r))
    (hgs : ∀ i, ContDiffOn ℝ ∞ (g i) (ball 0 r)) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ρ ≤ 1 →
      ∀ κ : ℝ, |κ| ≤ 1 → ∀ i,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => f i (ρ • p.1) + max p.2 0 • (κ • g i (ρ • p.1))) K := by
  obtain ⟨C, hC, hc⟩ := uniform_first_jet_dilation_budget hf hfs
  obtain ⟨D, hD, hd⟩ := uniform_first_jet_dilation_budget hg hgs
  have hM : 0 ≤ C + D := by linarith
  obtain ⟨K, hK, hk⟩ := exists_clamped_affine_holder_budget (n := n) (V := F) hM hβ
  refine ⟨K, hK, ?_⟩
  intro ρ hρ hρr hρ1 κ hκ i
  obtain ⟨hcs, hcl⟩ := hc ρ hρ hρr hρ1
  obtain ⟨hds, hdl⟩ := hd ρ hρ hρr hρ1
  apply hk (fun x => f i (ρ • x)) (fun x => κ • g i (ρ • x))
  · intro x hx
    constructor
    · exact (hcs i x hx).trans (by linarith)
    · rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul hκ (hds i x hx) (norm_nonneg _) zero_le_one).trans
        (by linarith)
  · intro x hx y hy
    constructor
    · exact (hcl i x hx y hy).trans
        (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + D) (norm_nonneg _))
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul hκ (hdl i x hx y hy) (norm_nonneg _) zero_le_one).trans
        (by nlinarith [norm_nonneg (x - y)])

theorem holderBound_neg {f : Point n → F} {β C : ℝ} {Q : Set (Point n)}
    (hf : HolderBound β Q f C) : HolderBound β Q (fun p => -f p) C := by
  refine ⟨hf.1, ?_, ?_⟩
  · intro p hp
    simpa only [norm_neg] using hf.2.1 p hp
  · intro p hp q hq
    have he : -f p - -f q = -(f p - f q) := by abel
    rw [he, norm_neg]
    exact hf.2.2 p hp q hq

theorem dilated_spatial_holder_budget {f : ι → Space n → F} {r β : ℝ}
    (hf : UniformJetBounds 1 f (fun _ => ball 0 r))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 r)) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ρ ≤ 1 → ∀ i,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => f i (ρ • p.1)) K := by
  obtain ⟨K, hK, hk⟩ := dilated_affine_holder_budget hf hf hfs hfs hβ
  refine ⟨K, hK, ?_⟩
  intro ρ hρ hρr hρ1 i
  simpa only [zero_smul, smul_zero, add_zero] using hk ρ hρ hρr hρ1 0 (by norm_num) i

end Yau.NodeProofs.F01Aux
