import Yau.Proofs.C03ShortLiftFamilies
import Yau.Proofs.C07LocalInversion

/-! A continuous actual section gives an open sheet with the two inverse identities. -/
noncomputable section
open scoped Manifold Topology ContDiff
open Set
namespace Yau.Proofs.C03Aux.ShortLift
open Yau Yau.Blueprint
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

def sheetCoordinates (Phi : ComplexVector n → M.Carrier) (ctarget : M.Carrier)
    (z : ComplexVector n) : ComplexVector n := chartPt ctarget (Phi z)

theorem inverse_sheet_topology {Phi : ComplexVector n → M.Carrier} {r : ℝ}
    (hPhi : IsLocalBiholomorphism Phi r) (ctarget : M.Carrier)
    (W : Set (ComplexVector n)) (hW : IsOpen W) (hne : W.Nonempty)
    (hTarget : W ⊆ chartTarget ctarget)
    (sigma : ComplexVector n → ComplexVector n) (hcont : ContinuousOn sigma W)
    (hmem : MapsTo sigma W (Metric.ball 0 r))
    (hright : ∀ w ∈ W, Phi (sigma w) = chartInv ctarget w) :
    InjOn sigma W ∧ IsOpen (sigma '' W) ∧ sigma '' W ⊆ Metric.ball 0 r ∧
      (∀ w ∈ W, sheetCoordinates Phi ctarget (sigma w) = w) ∧
      ∀ z ∈ sigma '' W, sigma (sheetCoordinates Phi ctarget z) = z := by
  have htheta : ∀ w ∈ W, sheetCoordinates Phi ctarget (sigma w) = w := by
    intro w hw
    rw [sheetCoordinates, hright w hw]
    exact (extChartAt (ComplexModel n) ctarget).right_inv (hTarget hw)
  have hinj : InjOn sigma W := by
    intro u hu v hv huv
    have H := congrArg (sheetCoordinates Phi ctarget) huv
    simpa only [htheta u hu, htheta v hv] using H
  let V : TopologicalSpace.Opens (ComplexVector n) := ⟨W, hW⟩
  have hV : Nonempty V := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let F : W → M.Carrier := fun w => chartInv ctarget w
  have htr (w : W) : (w : ComplexVector n) ∈ (chartAt (ComplexVector n) ctarget).target := by
    have hw := hTarget w.2
    change (w : ComplexVector n) ∈ (extChartAt (ComplexModel n) ctarget).target at hw
    rw [extChartAt_target] at hw
    exact hw.1
  have hFlocal : IsLocalHomeomorph F := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    apply IsLocalHomeomorphOn.mk
    intro w _
    refine ⟨(chartAt (ComplexVector n) ctarget).symm.subtypeRestr hV, ?_, ?_⟩
    · rw [OpenPartialHomeomorph.subtypeRestr_source]
      change (w : ComplexVector n) ∈ (chartAt (ComplexVector n) ctarget).target
      exact htr w
    · intro w' _
      rfl
  have hFinj : Function.Injective F := by
    intro u v huv
    apply Subtype.ext
    exact (chartAt (ComplexVector n) ctarget).symm.injOn (htr u) (htr v) huv
  have hFopen : Topology.IsOpenEmbedding F := hFlocal.isOpenEmbedding_of_injective hFinj
  let U : Set (ComplexVector n) := Metric.ball 0 r
  let pU : U → M.Carrier := fun z => Phi z
  have hpU : IsLocalHomeomorph pU :=
    restricted_local_homeomorph Phi U Metric.isOpen_ball
      ⟨sigma hne.choose, hmem hne.choose_spec⟩
      (fun z hz => C07Aux.local_homeomorph_of_localBiholomorphism hPhi hz)
  let sU : W → U := fun w => ⟨sigma w, hmem w.2⟩
  have hcs : Continuous sU :=
    (continuousOn_iff_continuous_domRestrict.mp hcont).subtype_mk _
  have hproj : pU ∘ sU = F := funext fun w => hright w w.2
  have hcomp : Topology.IsOpenEmbedding (pU ∘ sU) := hproj.symm ▸ hFopen
  have hsopen : Topology.IsOpenEmbedding sU := hpU.isOpenEmbedding_of_comp hcomp hcs
  have hsplain : Topology.IsOpenEmbedding (fun w : W => sigma w) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal.comp hsopen
  have hrange : Set.range (fun w : W => sigma w) = sigma '' W := by
    ext z
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, w.2, hw⟩
    · rintro ⟨w, hw, hz⟩
      exact ⟨⟨w, hw⟩, hz⟩
  refine ⟨hinj, ?_, ?_, htheta, ?_⟩
  · rw [← hrange]
    exact hsplain.isOpen_range
  · rintro _ ⟨w, hw, rfl⟩
    exact hmem hw
  · rintro _ ⟨w, hw, rfl⟩
    rw [htheta w hw]

end Yau.Proofs.C03Aux.ShortLift

