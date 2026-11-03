import Yau.Proofs.D02ModelAnchors
import Yau.Proofs.D02DiscPsh
import Yau.Proofs.D04CoordinateBridge

/-! Original D04 applied to the actual immersion potentials of one
admissible sequence. The positive-area anchors exclude the collapse
alternative without assuming any compactness of the disc images. -/

open scoped ENNReal Topology
open MeasureTheory Set Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint

def discPotential {n N : ℕ} (X : KahlerManifold n)
    (F : Pt X → ComplexVector N) (f : ℂ → Pt X) (w : ComplexVector 1) : EReal :=
  (immersionPotential X.metric.form F (discModelMap f w) : EReal)

theorem discPotential_subsequence {n N : ℕ} (X : KahlerManifold n)
    {F : Pt X → ComplexVector N} (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F)
    {K : Set (Pt X)} (hK : IsCompact K) (A : ℝ) (fs : ℕ → ℂ → Pt X)
    (hfs : ∀ j, IsHolomorphicDisc (fs j) ∧
      (∀ z : ℂ, ‖z‖ = 1 → fs j z ∈ K) ∧ discArea X.metric.form (fs j) ≤ ENNReal.ofReal A) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      PshL1Limit (Metric.ball (0 : ComplexVector 1) 1) (fun j => discPotential X F (fs j)) φ := by
  let D : Set (ComplexVector 1) := Metric.ball 0 1
  let Ω : ℕ → Set (ComplexVector 1) := fun _ => D
  let us : ℕ → ComplexVector 1 → EReal := fun j => discPotential X F (fs j)
  have hD : IsOpen D := Metric.isOpen_ball
  have hconn : IsConnected D := Metric.isConnected_ball (by norm_num)
  have hΩ : ∀ j, IsOpen (Ω j) ∧ Ω j ⊆ Ω (j + 1) ∧ Ω j ⊆ D :=
    fun _ => ⟨hD, Subset.rfl, Subset.rfl⟩
  have hcover : (⋃ j, Ω j) = D := by
    ext w
    simp only [mem_iUnion]
    exact ⟨fun ⟨_, hw⟩ => hw, fun hw => ⟨0, hw⟩⟩
  have hpsh : ∀ j, IsPshOn (us j) (Ω j) :=
    fun j => immersionPotential_disc_isPshOn X hF hImm (hfs j).1
  obtain ⟨BF, Bu, Bψ, hBF, hBu, hBψ, hbound⟩ := uniformImmersionConstants X hF hImm hK
  have hupper : ∀ T ⊆ D, IsCompact T → ∃ C : ℝ, ∀ j,
      T ⊆ Ω j → ∀ w ∈ T, us j w ≤ (C : EReal) := by
    intro T hTD hT
    refine ⟨Bψ, fun j hTΩ w hw => ?_⟩
    have hwD := hTD hw
    have hn : ‖Yau.Proofs.B01Aux.complexOneEquiv.symm w‖ ≤ 1 := by
      rw [Yau.Proofs.B01Aux.complexOneEquiv.symm.norm_map]
      exact (show ‖w‖ < 1 from by simpa only [D, Metric.mem_ball, dist_zero_right] using hwD).le
    change (immersionPotential X.metric.form F
      (fs j (Yau.Proofs.B01Aux.complexOneEquiv.symm w)) : EReal) ≤ (Bψ : EReal)
    exact_mod_cast (hbound (fs j) (hfs j).1 (hfs j).2.1 _ hn).2.2
  obtain ⟨φ, hφ, halt, _, hareaAnchor⟩ := Yau.Proofs.D04Aux.coordinate_psh_compactness 1
    D hD hconn Ω us hΩ hcover hpsh hupper
  obtain ⟨C, hC, hanchor⟩ := uniform_modelMovingAnchors X hF hImm hK A
  have hnotCollapse : ¬ PshCollapses D us φ := by
    apply hareaAnchor modelAnchorCompact (fun j => modelMovingAnchors X.metric.form (fs (φ j)) A)
      C (5 * Real.pi / 32) modelAnchorCompact_isCompact modelAnchorCompact_subset_disc
      (by positivity)
    intro j
    exact hanchor (fs (φ j)) (hfs (φ j)).1 (hfs (φ j)).2.1 (hfs (φ j)).2.2
  exact ⟨φ, hφ, halt.resolve_left hnotCollapse⟩

end Yau.NodeProofs.D02Aux
