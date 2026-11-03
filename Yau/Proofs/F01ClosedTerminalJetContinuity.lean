import Yau.Proofs.F01SpatialJetTerminalExtension
import Yau.LeafProofs.L16

/-! The actual endpoint jet limits and original Holder estimates give
continuous closed-face jets, also in the normalized terminal clock. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem normalized_closed_terminal_spatial_jet_continuity
    (S : Set (Space n)) (f : Point n → F) (b : Space n → F)
    {T κ β C : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (k : ℕ)
    (hf : HolderBound β (S ×ˢ Ioo (T - κ / 4) T)
      (fun p => iteratedFDeriv ℝ k (fun z => f (z, p.2)) p.1) C)
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ Ioo (T - κ / 4) T)
    (hLim : Tendsto τ atTop (𝓝 T))
    (hJets : TendstoUniformlyOn
      (fun m x => iteratedFDeriv ℝ k (fun z => f (z, τ m)) x)
      (iteratedFDeriv ℝ k b) atTop S) :
    ContinuousOn
      (fun p : Point n => iteratedFDeriv ℝ k
        (fun z => closeTerminalTimeFace f b T (z, T + κ * p.2)) p.1)
      (S ×ˢ Ioc (-(1 / 4 : ℝ)) 0) := by
  have hClosed := holder_actual_spatial_jet_close_terminal_face S f b hβ.le k
    hf τ hτ hLim hJets
  have hCont := Yau.LeafProofs.L16Aux.holderBound_continuousOn hβ hClosed
  have hAffine : Continuous (fun p : Point n => (p.1, T + κ * p.2)) := by fun_prop
  exact hCont.comp hAffine.continuousOn (by
    intro p hp
    refine ⟨hp.1, ?_, ?_⟩
    · have hh := mul_lt_mul_of_pos_left hp.2.1 hκ
      linarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos hκ.le hp.2.2
      linarith)

end Yau.NodeProofs.F01Aux
