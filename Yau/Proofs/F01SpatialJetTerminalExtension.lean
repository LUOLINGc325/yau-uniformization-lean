import Yau.Proofs.F01HolderTerminalFaceExtension

/-! Closing a terminal time face commutes with every actual spatial
derivative. The constructed spatial jet limits therefore give the
same Holder control for the actual extended potential's derivatives. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem spatial_jet_close_terminal_time_face
    (f : Point n → F) (b : Space n → F) (T : ℝ) (k : ℕ) (p : Point n) :
    iteratedFDeriv ℝ k (fun z => closeTerminalTimeFace f b T (z, p.2)) p.1 =
      closeTerminalTimeFace
        (fun q => iteratedFDeriv ℝ k (fun z => f (z, q.2)) q.1)
        (iteratedFDeriv ℝ k b) T p := by
  classical
  by_cases he : p.2 = T
  · simp [closeTerminalTimeFace, he]
  · simp only [closeTerminalTimeFace, ite_eq_right he]

theorem holder_actual_spatial_jet_close_terminal_face
    (S : Set (Space n)) (f : Point n → F) (b : Space n → F)
    {l T β C : ℝ} (hβ : 0 ≤ β) (k : ℕ)
    (hf : HolderBound β (S ×ˢ Ioo l T)
      (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) C)
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ Ioo l T) (hLim : Tendsto τ atTop (𝓝 T))
    (hJets : TendstoUniformlyOn
      (fun m x => iteratedFDeriv ℝ k (fun z => f (z, τ m)) x)
      (iteratedFDeriv ℝ k b) atTop S) :
    HolderBound β (S ×ˢ Ioc l T)
      (fun p => iteratedFDeriv ℝ k (fun z => closeTerminalTimeFace f b T (z, p.2)) p.1) C := by
  have hh := holderBound_close_terminal_time_face S
    (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1)
    (iteratedFDeriv ℝ k b) hβ hf τ hτ hLim (fun x hx => hJets.tendsto_at hx)
  simpa only [spatial_jet_close_terminal_time_face] using hh

end Yau.NodeProofs.F01Aux
