import Yau.Proofs.C07LocalInversion
import Yau.Proofs.C07LiftUniqueness
import Mathlib.Topology.Homotopy.Lifting

/-! Actual row lifts through a chart vary continuously with all parameters. -/

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07Aux

open Yau Yau.Blueprint

variable {n : ℕ} {M : ComplexManifold n}

theorem chart_ball_isLocalHomeomorph {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : IsLocalBiholomorphism Φ r) :
    IsLocalHomeomorph (fun z : Metric.ball (0 : ComplexVector n) r => Φ z) := by
  apply IsLocalHomeomorph.mk
  intro z
  obtain ⟨e, hz, _, heq⟩ := local_homeomorph_of_localBiholomorphism hΦ z.2
  let V : TopologicalSpace.Opens (ComplexVector n) := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  let e' : OpenPartialHomeomorph (Metric.ball (0 : ComplexVector n) r) M.Carrier :=
    e.subtypeRestr (s := V) ⟨z⟩
  refine ⟨e', ?_, ?_⟩
  · simpa only [e', OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hz
  · intro w hw
    have hw' : (w : ComplexVector n) ∈ e.source := by
      simpa only [e', OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hw
    exact (heq hw').symm

theorem chart_lift_joint_continuous {A : Type*} [TopologicalSpace A]
    {Φ : ComplexVector n → M.Carrier} {r : ℝ} (hΦ : IsLocalBiholomorphism Φ r)
    (H : C(unitInterval × A, M.Carrier)) (η : unitInterval × A → ComplexVector n)
    (hball : ∀ p, η p ∈ Metric.ball 0 r) (hlift : ∀ p, Φ (η p) = H p)
    (hstart : Continuous (fun a => η (0, a)))
    (hrows : ∀ a, Continuous (fun t => η (t, a))) : Continuous η := by
  let G : unitInterval × A → Metric.ball (0 : ComplexVector n) r :=
    fun p => ⟨η p, hball p⟩
  have hG : Continuous G := by
    apply (chart_ball_isLocalHomeomorph hΦ).continuous_lift
      (T2Space.isSeparatedMap _) H
    · exact funext hlift
    · exact hstart.subtype_mk _
    · exact fun a => (hrows a).subtype_mk _
  exact continuous_subtype_val.comp hG

end Yau.Proofs.C07Aux
