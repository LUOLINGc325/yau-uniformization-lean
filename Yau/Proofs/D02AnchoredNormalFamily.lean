import Yau.Proofs.D02Equicontinuity

/-! Genuine compact moving anchors and equicontinuity give one normal
extraction on a connected open domain. Bounded point ranges are proved
before Arzelà--Ascoli is invoked. -/

open scoped Topology
open Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux

theorem normalFamily_of_moving_anchors {Y : Type*} [MetricSpace Y]
    [CompleteSpace Y] [ProperSpace Y] {O : Set ℂ} (hconn : IsPreconnected O)
    (fs : ℕ → ℂ → Y) (heq : Equicontinuous (fun j (z : O) => fs j z))
    {H : Set ℂ} (hH : IsCompact H) (hHO : H ⊆ O)
    (zs : ℕ → ℂ) (hzs : ∀ j, zs j ∈ H) {K : Set Y} (hK : IsCompact K)
    (hmap : ∀ j, fs j (zs j) ∈ K) (hO : IsOpen O) :
    ∃ β : ℕ → ℕ, StrictMono β ∧ ∃ f : C(O, Y),
      ∀ L : Set O, IsCompact L →
        TendstoUniformlyOn (fun j (z : O) => fs (β j) z) f atTop L := by
  letI : PreconnectedSpace O := Subtype.preconnectedSpace hconn
  letI : LocallyCompactSpace O := hO.locallyCompactSpace
  let H' : Set O := (Subtype.val : O → ℂ) ⁻¹' H
  have hH' : IsCompact H' := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
    hH (by simpa only [Subtype.range_coe] using hHO)
  let ws : ℕ → O := fun j => ⟨zs j, hHO (hzs j)⟩
  let o : Y := fs 0 (zs 0)
  obtain ⟨β, hβ, x, _, B, hB⟩ := moving_anchor_bounded_subsequence
    (fun j (z : O) => fs j z) ws hH' hzs hK hmap (fun x _ => heq x) o
  have heqβ : Equicontinuous (fun j (z : O) => fs (β j) z) := heq.comp β
  have hpoint := bounded_point_ranges_of_connected (fun j (z : O) => fs (β j) z) heqβ o ⟨x, B, hB⟩
  let Fs : ℕ → C(O, Y) := fun j => ⟨fun z => fs (β j) z, heqβ.continuous j⟩
  have hpt : ∀ z : O, ∃ Q : Set Y, IsCompact Q ∧ ∀ j, Fs j z ∈ Q := by
    intro z
    obtain ⟨R, hR⟩ := hpoint z
    exact ⟨closedBall o R, isCompact_closedBall _ _, hR⟩
  obtain ⟨γ, hγ, f, hf⟩ := continuousFamily_subsequence_uniformOn_compacts Fs
    (fun L _ => heqβ.equicontinuousOn L) hpt
  refine ⟨β ∘ γ, hβ.comp hγ, f, ?_⟩
  intro L hL
  exact hf L hL

end Yau.NodeProofs.D02Aux
