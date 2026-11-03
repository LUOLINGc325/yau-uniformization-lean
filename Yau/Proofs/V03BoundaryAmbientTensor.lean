import Yau.Proofs.V03AmbientTensorGlobalLipschitz
import Yau.Proofs.V03ClockDifference
import Yau.Proofs.V03AmbientSmooth
import Yau.Proofs.V03CirclePeriod

/-! The actual ambient tensor along each admissible boundary has one
uniform bound and difference estimate before every disc and frame. -/

open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau Yau.Blueprint

variable {n q : ℕ} {X : KahlerManifold n}

def boundaryAmbientTensor (d : VariationData X q) (j a : ℕ) (F : VariationDisc X)
    (θ : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  ambientBoundaryTensor d j a (F.f (circlePoint θ)) (discTime F (circlePoint θ)) F.s

theorem boundaryAmbientTensor_periodic (d : VariationData X q) (j a : ℕ) (F : VariationDisc X) :
    Function.Periodic (boundaryAmbientTensor d j a F) (2 * Real.pi) :=
  circleTrace_periodic (fun ζ => ambientBoundaryTensor d j a (F.f ζ) (discTime F ζ) F.s)

theorem admissible_ambient_trace_continuous {d : VariationData X q} (hd : VariationSetup d)
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    Continuous (fun θ => d.G (F.f (circlePoint θ))) :=
  (cotangentDisc_ambient_contDiffOn hF.1 hd.2.2.2.2.1.1).continuousOn.comp_continuous
    circlePoint_contDiff.continuous circlePoint_mem_closedBall

theorem admissible_clock_trace_continuous {d : VariationData X q}
    {j : ℕ} {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    Continuous (fun θ => discTime F (circlePoint θ)) :=
  (discTime_contDiffOn hF.2.1).continuousOn.comp_continuous
    circlePoint_contDiff.continuous circlePoint_mem_closedBall

theorem boundaryAmbientTensor_continuous {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) {F : VariationDisc X} (hF : AdmissibleVariationDisc d j F) :
    Continuous (boundaryAmbientTensor d j a F) := by
  have hK : CotangentCompact (boundaryCompact d j) :=
    (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.2.1
  have hy (θ : ℝ) : F.f (circlePoint θ) ∈ boundaryCompact d j :=
    ⟨(hF.2.2.2.2.2.2.2.1 θ).1.le, (hF.2.2.2.2.2.2.2.1 θ).2.le⟩
  have ht (θ : ℝ) : discTime F (circlePoint θ) ∈ Set.Icc 0 d.T :=
    ⟨(admissible_discTime_mem hF (circlePoint_mem_closedBall θ)).1.le,
      (admissible_discTime_mem hF (circlePoint_mem_closedBall θ)).2.le⟩
  have hs : F.s ∈ Set.Icc 0 d.T := ⟨hF.2.2.2.1.le, hF.2.2.2.2.1.le⟩
  let p : ℝ → CompactImmersionTimes d.G (boundaryCompact d j) d.T := fun θ =>
    ((⟨d.G (F.f (circlePoint θ)), ⟨F.f (circlePoint θ), hy θ, rfl⟩⟩,
      ⟨discTime F (circlePoint θ), ht θ⟩), ⟨F.s, hs⟩)
  have hp : Continuous p :=
    (((admissible_ambient_trace_continuous hd hF).subtype_mk _).prodMk
      ((admissible_clock_trace_continuous hF).subtype_mk _)).prodMk continuous_const
  have hh := (compactAmbientBoundaryTensor_locallyLipschitz hd j a ha hK).continuous.comp hp
  apply hh.congr
  intro θ
  change ambientBoundaryTensor d j a
    (compactImmersionPoint d.G ⟨d.G (F.f (circlePoint θ)), ⟨F.f (circlePoint θ), hy θ, rfl⟩⟩)
      (discTime F (circlePoint θ)) F.s = boundaryAmbientTensor d j a F θ
  rw [compactImmersionPoint_eq hd.2.2.2.2.1.2.1 (F.f (circlePoint θ)) (hy θ)]
  rfl

theorem boundaryAmbientTensor_uniform_control {d : VariationData X q} (hd : VariationSetup d)
    (j a : ℕ) (ha : 4 ≤ a) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ F : VariationDisc X,
      AdmissibleVariationDisc d j F →
      (∀ θ b c, ‖boundaryAmbientTensor d j a F θ b c‖ ≤ M) ∧
      ∀ θ τ b c, ‖boundaryAmbientTensor d j a F θ b c - boundaryAmbientTensor d j a F τ b c‖ ≤
        C * (‖d.G (F.f (circlePoint θ)) - d.G (F.f (circlePoint τ))‖ +
          (2 * d.T) * ‖F.w (circlePoint θ) - F.w (circlePoint τ)‖) := by
  have hK : CotangentCompact (boundaryCompact d j) :=
    (hd.2.2.2.2.2.2.2.2.2.2.2.2.2 j).2.2.1
  obtain ⟨C, hC, hLip⟩ := ambientBoundaryTensor_compact_lipschitz hd j a ha hK
  obtain ⟨M, hM, hnorm⟩ := ambientBoundaryTensor_compact_bound hd j a ha hK
  refine ⟨C, M, hC, hM, fun F hF => ?_⟩
  have hy (θ : ℝ) : F.f (circlePoint θ) ∈ boundaryCompact d j :=
    ⟨(hF.2.2.2.2.2.2.2.1 θ).1.le, (hF.2.2.2.2.2.2.2.1 θ).2.le⟩
  have ht (θ : ℝ) : discTime F (circlePoint θ) ∈ Set.Icc 0 d.T :=
    ⟨(admissible_discTime_mem hF (circlePoint_mem_closedBall θ)).1.le,
      (admissible_discTime_mem hF (circlePoint_mem_closedBall θ)).2.le⟩
  have hs : F.s ∈ Set.Icc 0 d.T := ⟨hF.2.2.2.1.le, hF.2.2.2.2.1.le⟩
  constructor
  · intro θ b c
    exact (Matrix.norm_entry_le_entrywise_sup_norm (boundaryAmbientTensor d j a F θ)).trans
      (hnorm _ (hy θ) _ (ht θ) _ hs)
  intro θ τ b c
  have he := Matrix.norm_entry_le_entrywise_sup_norm
    (boundaryAmbientTensor d j a F θ - boundaryAmbientTensor d j a F τ) (i := b) (j := c)
  have hh := hLip _ (hy θ) _ (hy τ) _ (ht θ) _ (ht τ) _ hs _ hs
  simp only [sub_self, abs_zero, add_zero] at hh
  exact (he.trans hh).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (admissible_clock_difference hF θ τ)) hC)

end Yau.Blueprint.V03Proof
