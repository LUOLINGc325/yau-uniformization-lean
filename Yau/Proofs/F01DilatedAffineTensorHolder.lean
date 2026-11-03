import Yau.Proofs.F01UniformTensorFirstJet
import Yau.Proofs.F01TensorDilation
import Yau.Proofs.F01ParabolicDilation

/-! All fixed-order spatial tensor jets of the actual dilated clamped
affine background have uniform Holder budgets. The next background jet
provides each budget before the center, scale, and bounded time factor. -/
noncomputable section
open Set Metric
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {ι F : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dilated_affine_spatial_tensor_holder_budget {f g : ι → Space n → F}
    {r β : ℝ} (k : ℕ)
    (hf : UniformJetBounds (k + 1) f (fun _ => ball 0 r))
    (hg : UniformJetBounds (k + 1) g (fun _ => ball 0 r))
    (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 r))
    (hgs : ∀ i, ContDiffOn ℝ ∞ (g i) (ball 0 r)) (hβ : β ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ r → ρ ≤ 1 →
      ∀ κ : ℝ, |κ| ≤ 1 → ∀ i,
      HolderBound β (cylinder (ball (0 : Space n) 1) (-1) 1)
        (fun p => iteratedFDeriv ℝ k
          (fun z => f i (ρ • z) + max p.2 0 • (κ • g i (ρ • z))) p.1) K := by
  have hfj (i : ι) : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k (f i)) (ball 0 r) := by
    apply isOpen_ball.contDiffOn_iff.mpr
    intro z hz
    exact ((hfs i).contDiffAt (isOpen_ball.mem_nhds hz)).iteratedFDeriv_right (by simp)
  have hgj (i : ι) : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k (g i)) (ball 0 r) := by
    apply isOpen_ball.contDiffOn_iff.mpr
    intro z hz
    exact ((hgs i).contDiffAt (isOpen_ball.mem_nhds hz)).iteratedFDeriv_right (by simp)
  obtain ⟨K, hK, hk⟩ := dilated_affine_holder_budget
    (uniform_tensor_first_jet k hf) (uniform_tensor_first_jet k hg) hfj hgj hβ
  refine ⟨K, hK, ?_⟩
  intro ρ hρ hρr hρ1 κ hκ i
  have hj := holderBound_spatialTensorDilation (ρ := ρ) k (hk ρ hρ hρr hρ1 κ hκ i)
    (by simpa only [abs_of_pos hρ] using hρ1)
  have he : ∀ p ∈ cylinder (ball (0 : Space n) 1) (-1) 1,
      iteratedFDeriv ℝ k
        (fun z => f i (ρ • z) + max p.2 0 • (κ • g i (ρ • z))) p.1 =
      spatialTensorDilation k ρ
        (iteratedFDeriv ℝ k (f i) (ρ • p.1) +
          max p.2 0 • (κ • iteratedFDeriv ℝ k (g i) (ρ • p.1))) := by
    intro p hp
    have hz := spatialDilation_mem_ball hρ hρr hp.1
    have hfa := (hfs i).contDiffAt (isOpen_ball.mem_nhds hz)
    have hga := (hgs i).contDiffAt (isOpen_ball.mem_nhds hz)
    have hs : ContDiffOn ℝ ∞ (fun z => f i z + max p.2 0 • (κ • g i z)) (ball 0 r) :=
      (hfs i).add (((hgs i).const_smul κ).const_smul (max p.2 0))
    have hid := iteratedFDeriv_spatial_dilation k ρ isOpen_ball hs hz
    have hjet : iteratedFDeriv ℝ k (fun z => f i z + max p.2 0 • (κ • g i z)) (ρ • p.1) =
        iteratedFDeriv ℝ k (f i) (ρ • p.1) +
          max p.2 0 • (κ • iteratedFDeriv ℝ k (g i) (ρ • p.1)) := by
      rw [fun_iteratedFDeriv_add_apply (hfa.of_le (by simp))
        (((hga.const_smul κ).const_smul (max p.2 0)).of_le (by simp)),
        iteratedFDeriv_const_smul_apply' ((hga.const_smul κ).of_le (by simp)),
        iteratedFDeriv_const_smul_apply' (hga.of_le (by simp))]
    exact hid.trans (congrArg (spatialTensorDilation k ρ) hjet)
  refine ⟨hj.1, ?_, ?_⟩
  · intro p hp
    change ‖iteratedFDeriv ℝ k
      (fun z => f i (ρ • z) + max p.2 0 • (κ • g i (ρ • z))) p.1‖ ≤ K
    rw [he p hp]
    exact hj.2.1 p hp
  · intro p hp q hq
    change ‖iteratedFDeriv ℝ k
      (fun z => f i (ρ • z) + max p.2 0 • (κ • g i (ρ • z))) p.1 -
      iteratedFDeriv ℝ k
      (fun z => f i (ρ • z) + max q.2 0 • (κ • g i (ρ • z))) q.1‖ ≤ _
    rw [he p hp, he q hq]
    exact hj.2.2 p hp q hq

end Yau.NodeProofs.F01Aux
