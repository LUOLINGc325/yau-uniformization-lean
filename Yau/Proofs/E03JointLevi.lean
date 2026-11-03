import Yau.Proofs.E03LeviLinearChange
import Yau.Proofs.E03SmoothLocalization
import Yau.Proofs.E03JointSubmean
import Yau.LeafProofs.L22Circle

/-! Actual joint submean plus genuine smooth localization yields the original joint Levi matrix. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint
variable {n : ℕ} {X : KahlerManifold n}

theorem jointNorm_levi_posSemidef (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (hcomp : EllipsoidComparison X h) (hscalar : ScalarComparison X h ρ)
    (c : Pt X) (p : JointSpace n) (hp : p ∈ jointDomain c) :
    (leviMatrix (jointNorm h c) p jointDir).PosSemidef := by
  let e := jointContinuousLinearEquiv n
  let F := jointNorm h c ∘ e
  let O := e ⁻¹' jointDomain c
  have hO : IsOpen O := (isOpen_jointDomain c).preimage e.continuous
  have hq : e.symm p ∈ O := by simpa only [O, mem_preimage, e.apply_symm_apply] using hp
  have he : ContDiff ℝ ∞ (e : ComplexVector (Fintype.card (JointIndex n)) → JointSpace n) :=
    e.toContinuousLinearMap.contDiff.restrict_scalars ℝ
  have hF : ContDiffOn ℝ ∞ F O :=
    (jointNorm_contDiffOn h hloc.1.2.1 c).comp he.contDiffOn (fun q hq => hq)
  obtain ⟨g, hg, hge⟩ := exists_global_contDiff_equal_germ hO hq hF
  obtain ⟨V, hVeq, hVo, hqV⟩ := eventually_nhds_iff.mp hge
  let W := V ∩ O
  have hWo : IsOpen W := hVo.inter hO
  have hqW : e.symm p ∈ W := ⟨hqV, hq⟩
  have heq : EqOn g F W := fun q hq => hVeq q hq.1
  have hpsh : Yau.LeafCandidates.ComplexLinePshOn W g := by
    refine ⟨hg.continuous.continuousOn, ?_⟩
    intro z v hdisc
    have hd : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → e z + ζ • e v ∈ jointDomain c := by
      intro ζ hζ
      have hmem := (hdisc ζ hζ).2
      simpa only [O, mem_preimage, map_add, map_smul] using hmem
    have hs := jointNorm_affine_submean o h U P ρ hloc hopt hcomp hscalar c (e z) (e v) hd
    have hz : z ∈ W := by simpa using hdisc 0 (by simp)
    rw [heq hz]
    change F z ≤ _
    have hcircle : (fun θ : ℝ => g (z + Complex.exp (θ * Complex.I) • v)) =
        (fun θ : ℝ => jointNorm h c (e z + Complex.exp (θ * Complex.I) • e v)) := by
      funext θ
      have hmem := hdisc (Complex.exp (θ * Complex.I)) (by simp [Complex.norm_exp, Complex.mul_re])
      rw [heq hmem]
      simp only [F, Function.comp_apply, map_add, map_smul]
    rw [hcircle]
    exact hs
  have hPSD := Yau.LeafProofs.L22Aux.leviC_posSemidef_of_smooth_psh hWo hpsh hg hqW
  have hlevi := Yau.LeafProofs.L22Aux.leviC_congr_of_eventuallyEq hge
  rw [hlevi] at hPSD
  rw [jointLevi_eq_submatrix ((jointNorm_contDiffOn h hloc.1.2.1 c).contDiffAt
    ((isOpen_jointDomain c).mem_nhds hp) |>.of_le (by norm_num))]
  exact hPSD.submatrix _

end Yau.NodeProofs.E03Aux
