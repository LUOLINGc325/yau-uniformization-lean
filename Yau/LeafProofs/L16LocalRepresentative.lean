import Yau.LeafProofs.L16
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Compactness.Lindelof

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem productVolume_eq_restrict {n : ℕ} (O : Set (Space n)) (I : Set ℝ) :
    productVolume O I = (volume : Measure (Point n)).restrict (O ×ˢ I) := by
  exact Measure.prod_restrict O I

theorem smooth_representative_of_local_ae {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hLocal : ∀ p ∈ Q, ∃ W : Set (Point n), IsOpen W ∧ p ∈ W ∧ W ⊆ Q ∧
      ∃ w : Point n → ℝ, ContDiffOn ℝ ∞ w W ∧ u =ᵐ[volume.restrict W] w) :
    ∃ v : Point n → ℝ, ContDiffOn ℝ ∞ v Q ∧ u =ᵐ[volume.restrict Q] v ∧
      ∀ (W : Set (Point n)) (w : Point n → ℝ), IsOpen W → W ⊆ Q →
        ContinuousOn w W → u =ᵐ[volume.restrict W] w → Set.EqOn v w W := by
  classical
  choose W hOpen hMem hSub w hSmooth hAE using fun p : Q => hLocal p.1 p.2
  let v : Point n → ℝ := fun p => if hp : p ∈ Q then w ⟨p,hp⟩ p else 0
  have hEq (i : Q) : Set.EqOn v (w i) (W i) := by
    intro p hp
    have hpQ : p ∈ Q := hSub i hp
    let j : Q := ⟨p,hpQ⟩
    have hj : u =ᵐ[volume.restrict (W j ∩ W i)] w j :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left (hAE j)
    have hi : u =ᵐ[volume.restrict (W j ∩ W i)] w i :=
      ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hAE i)
    have hA : w j =ᵐ[volume.restrict (W j ∩ W i)] w i := hj.symm.trans hi
    have hEq := Measure.eqOn_open_of_ae_eq hA ((hOpen j).inter (hOpen i))
      ((hSmooth j).continuousOn.mono Set.inter_subset_left)
      ((hSmooth i).continuousOn.mono Set.inter_subset_right)
    simpa only [v,dite_eq_left hpQ] using hEq ⟨hMem j,hp⟩
  have hVS : ContDiffOn ℝ ∞ v Q := by
    apply contDiffOn_of_locally_contDiffOn
    intro p hp
    let i : Q := ⟨p,hp⟩
    exact ⟨W i,hOpen i,hMem i,((hSmooth i).congr (hEq i)).mono Set.inter_subset_right⟩
  obtain ⟨s,hs,hCover⟩ := (HereditarilyLindelofSpace.isLindelof Q).elim_countable_subcover
    W hOpen (fun p hp => Set.mem_iUnion.mpr ⟨⟨p,hp⟩,hMem ⟨p,hp⟩⟩)
  have hUnion : (⋃ i ∈ s, W i) = Q := Set.Subset.antisymm
    (Set.iUnion₂_subset fun i _ => hSub i) hCover
  have hVA : u =ᵐ[volume.restrict Q] v := by
    rw [← hUnion]
    apply (ae_eq_restrict_biUnion_iff W hs u v).2
    intro i _
    exact (hAE i).trans (ae_restrict_of_forall_mem (hOpen i).measurableSet fun p hp => (hEq i hp).symm)
  refine ⟨v,hVS,hVA,?_⟩
  intro U z hU hUQ hZ hUZ
  have hUV : u =ᵐ[volume.restrict U] v := ae_restrict_of_ae_restrict_of_subset hUQ hVA
  exact Measure.eqOn_open_of_ae_eq (hUV.symm.trans hUZ) hU (hVS.continuousOn.mono hUQ) hZ

theorem timeD_eq_deriv_of_isOpen {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {u : Point n → ℝ} {p : Point n} (hp : p ∈ Q) :
    timeD Q u p = deriv (fun t => u (p.1,t)) p.2 := by
  exact derivWithin_of_mem_nhds
    ((hQ.preimage (continuous_const.prodMk continuous_id)).mem_nhds hp)

theorem linearOp_congr_open_sets {n : ℕ} {Q R : Set (Point n)}
    (hQ : IsOpen Q) (hR : IsOpen R) {u v : Point n → ℝ}
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {p : Point n} (hpQ : p ∈ Q) (hpR : p ∈ R) (hEq : u =ᶠ[𝓝 p] v) :
    linearOp Q a b u p = linearOp R a b v p := by
  have hX : (fun x : Space n => u (x,p.2)) =ᶠ[𝓝 p.1] (fun x => v (x,p.2)) :=
    hEq.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hS : spatialD u p = spatialD v p := hX.fderiv_eq
  have hSS : spatialDD u p = spatialDD v p := hX.fderiv.fderiv_eq
  have hTime : (fun t : ℝ => u (p.1,t)) =ᶠ[𝓝 p.2] (fun t => v (p.1,t)) :=
    hEq.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt
  simp only [linearOp,timeD_eq_deriv_of_isOpen hQ hpQ,timeD_eq_deriv_of_isOpen hR hpR,
    hTime.deriv_eq,hS,hSS]

theorem smooth_solution_of_local_ae {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hLocal : ∀ p ∈ Q, ∃ W : Set (Point n), IsOpen W ∧ p ∈ W ∧ W ⊆ Q ∧
      ∃ w : Point n → ℝ, ContDiffOn ℝ ∞ w W ∧ u =ᵐ[volume.restrict W] w ∧
        ∀ q ∈ W, linearOp W a b w q = f q) :
    ∃ v : Point n → ℝ, ContDiffOn ℝ ∞ v Q ∧ u =ᵐ[volume.restrict Q] v ∧
      ∀ p ∈ Q, linearOp Q a b v p = f p := by
  obtain ⟨v,hV,hAE,hAgree⟩ := smooth_representative_of_local_ae (fun p hp => by
    obtain ⟨W,hW,hpW,hWQ,w,hw,hAE,_⟩ := hLocal p hp
    exact ⟨W,hW,hpW,hWQ,w,hw,hAE⟩)
  refine ⟨v,hV,hAE,?_⟩
  intro p hp
  obtain ⟨W,hW,hpW,hWQ,w,hw,hAE,hOp⟩ := hLocal p hp
  have hEq : v =ᶠ[𝓝 p] w := Filter.eventually_of_mem (hW.mem_nhds hpW)
    (fun q hq => hAgree W w hW hWQ hw.continuousOn hAE hq)
  exact (linearOp_congr_open_sets hQ hW a b hp hpW hEq).trans (hOp p hpW)

theorem homogeneous_representative_of_local_cylinders {n : ℕ}
    {O : Set (Space n)} {l r : ℝ} (hO : IsOpen O)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u : Point n → ℝ}
    (hLocal : ∀ p ∈ O ×ˢ Set.Ioo l r, ∃ (V : Set (Space n)) (c e : ℝ) (w : Point n → ℝ),
      IsOpen V ∧ p ∈ V ×ˢ Set.Ioo c e ∧ V ×ˢ Set.Ioo c e ⊆ O ×ˢ Set.Ioo l r ∧
      ContDiffOn ℝ ∞ w (V ×ˢ Set.Ioo c e) ∧
      u =ᵐ[productVolume V (Set.Ioo c e)] w ∧
      ∀ q ∈ V ×ˢ Set.Ioo c e, linearOp (V ×ˢ Set.Ioo c e) a b w q = 0) :
    ∃ v : Point n → ℝ, ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r) ∧
      u =ᵐ[productVolume O (Set.Ioo l r)] v ∧
      ∀ p ∈ O ×ˢ Set.Ioo l r, linearOp (O ×ˢ Set.Ioo l r) a b v p = 0 := by
  rw [productVolume_eq_restrict]
  apply smooth_solution_of_local_ae (hO.prod isOpen_Ioo)
  intro p hp
  obtain ⟨V,c,e,w,hV,hpV,hVQ,hw,hAE,hOp⟩ := hLocal p hp
  rw [productVolume_eq_restrict] at hAE
  exact ⟨V ×ˢ Set.Ioo c e,hV.prod isOpen_Ioo,hpV,hVQ,w,hw,hAE,hOp⟩

end Yau.LeafProofs.L16Aux
