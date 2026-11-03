import Yau.Proofs.D02PotentialRiesz
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

/-! The actual large-atom set is locally finite and countable. Its
complement in the unit disc is open and path connected. -/

open scoped ENNReal Topology
open MeasureTheory Filter Metric Set

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.LeafProofs

def concentrationAtoms (U : Set ℂ) (μ : Measure ℂ) : Set ℂ := {z | z ∈ U ∧ 1 ≤ μ {z}}

def regularPotentialDomain (U : Set ℂ) (μ : Measure ℂ) : Set ℂ := {z | z ∈ U ∧ μ {z} < 1}

theorem concentrationAtoms_finite_on_compact {U K : Set ℂ} (μ : Measure ℂ)
    (hμ : ∀ S : Set ℂ, IsCompact S → S ⊆ U → μ S < ⊤)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ concentrationAtoms U μ).Finite := by
  have h := L08_finite_large_atoms μ K (hμ K hK hKU) one_ne_zero
  exact h.subset (fun z hz => ⟨hz.1, hz.2.2⟩)

theorem concentrationAtoms_countable {U : Set ℂ} (hU : IsOpen U) (μ : Measure ℂ)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤) :
    (concentrationAtoms U μ).Countable := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  let K : ℕ → Set ℂ := fun j => (Subtype.val : U → ℂ) '' E j
  have hK (j : ℕ) : IsCompact (K j) := (E.isCompact j).image continuous_subtype_val
  have hKU (j : ℕ) : K j ⊆ U := by rintro _ ⟨z, _, rfl⟩; exact z.2
  have hfin (j : ℕ) : (K j ∩ concentrationAtoms U μ).Finite :=
    concentrationAtoms_finite_on_compact μ hμ (hK j) (hKU j)
  apply (countable_iUnion fun j => (hfin j).countable).mono
  intro z hz
  let w : U := ⟨z, hz.1⟩
  obtain ⟨j, hj⟩ := E.exists_superset_of_isCompact (isCompact_singleton : IsCompact ({w} : Set U))
  exact mem_iUnion.mpr ⟨j, ⟨⟨w, hj (mem_singleton w), rfl⟩, hz⟩⟩

theorem regularPotentialDomain_isOpen {U : Set ℂ} (hU : IsOpen U) (μ : Measure ℂ)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ U → μ K < ⊤) :
    IsOpen (regularPotentialDomain U μ) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨R, hR, hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz.1)
  let T : Set ℂ := {w | w ∈ closedBall z R ∧ 1 ≤ μ {w}}
  have hT : T.Finite := L08_finite_large_atoms μ (closedBall z R)
    (hμ _ (isCompact_closedBall z R) hRU) one_ne_zero
  have hzT : z ∉ T := fun h => (not_le_of_gt hz.2) h.2
  have hV : ball z R ∩ Tᶜ ∈ 𝓝 z :=
    inter_mem (isOpen_ball.mem_nhds (mem_ball_self hR)) (hT.isClosed.isOpen_compl.mem_nhds hzT)
  apply mem_of_superset hV
  intro w hw
  refine ⟨hRU (ball_subset_closedBall hw.1), lt_of_not_ge ?_⟩
  intro hmass
  exact hw.2 ⟨ball_subset_closedBall hw.1, hmass⟩

theorem regularPotentialDisc_isPathConnected (μ : Measure ℂ)
    (hμ : ∀ K : Set ℂ, IsCompact K → K ⊆ ball (0 : ℂ) 1 → μ K < ⊤) :
    IsPathConnected (regularPotentialDomain (ball (0 : ℂ) 1) μ) := by
  let e : ℂ ≃ₜ ball (0 : ℂ) 1 := Homeomorph.unitBall
  let f : ℂ → ℂ := fun z => (e z : ℂ)
  let Z := concentrationAtoms (ball (0 : ℂ) 1) μ
  have hZ : Z.Countable := concentrationAtoms_countable isOpen_ball μ hμ
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hpre : (f ⁻¹' Z).Countable := hZ.preimage hf
  have hpc : IsPathConnected (f ⁻¹' Z)ᶜ :=
    hpre.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have himage : f '' (f ⁻¹' Z)ᶜ = regularPotentialDomain (ball (0 : ℂ) 1) μ := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(e w).2, lt_of_not_ge ?_⟩
      intro hmass
      exact hw ⟨(e w).2, hmass⟩
    · intro hz
      let w := e.symm ⟨z, hz.1⟩
      have heq : f w = z := congrArg Subtype.val (e.apply_symm_apply ⟨z, hz.1⟩)
      refine ⟨w, ?_, heq⟩
      change f w ∉ Z
      rw [heq]
      exact fun h => (not_le_of_gt hz.2) h.2
  rw [← himage]
  exact hpc.image (continuous_subtype_val.comp e.continuous)

end Yau.NodeProofs.D02Aux
