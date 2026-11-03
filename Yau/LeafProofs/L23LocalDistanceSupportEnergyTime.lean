import Yau.LeafProofs.L23LocalDistanceSupportEnergyGradient
import Yau.LeafProofs.L23DistanceEnergyTime

/-! The genuine evolving-metric time bound for the same physical endpoint energy. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000

theorem fieldPathSpeedSq_time_contDiffOn_two
    (h : ℝ → HermitianField M) (I : Set ℝ) (hI : IsOpen I) (hh : MetricFamilySmooth h I)
    (γ : ℝ → M.Carrier) (J : Set ℝ) (hJ : IsOpen J) :
    letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ J →
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => fieldPathSpeed (h p.1) γ p.2 ^ 2) (I ×ˢ J) := by
  letI := manifold_realSmooth M
  intro hγ
  have HF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3
      (fun p : ℝ × ℝ => γ p.2) ((Set.univ : Set ℝ) ×ˢ J) :=
    hγ.comp contDiffOn_snd.contMDiffOn (fun p hp => hp.2)
  have HD := familyPathEnergyDensity_contDiffOn_two h I hI hh (fun _ : ℝ => γ) Set.univ J isOpen_univ hJ HF
  have HM : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => (((0 : ℝ),p.1),p.2)) (I ×ˢ J) :=
    (contDiffOn_const.prodMk contDiffOn_fst).prodMk contDiffOn_snd
  exact HD.comp HM (fun p hp => ⟨⟨Set.mem_univ _,hp.1⟩,hp.2⟩)

theorem endpointVariation_fieldPathEnergy_time_deriv_lower
    (h : ℝ → HermitianField M) (O : Set M.Carrier) (a b σ K d : ℝ)
    (hσ : 0 ≤ σ) (hflow : LocalRealRicciFlow h O (Set.Icc a b) σ)
    (hcurv : ∀ x ∈ O, ∀ s ∈ Set.Icc a b, curvatureJetNorm (h s) 0 x ≤ K)
    (γ : ℝ → M.Carrier) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (A : ℝ → ComplexVector n → M.Carrier) (δ : ℝ) (hδ : 0 < δ)
    (h0 : (0 : ComplexVector n) ∈ e.source) (he0 : e 0 = γ 1)
    (hA0 : ∀ u ∈ Set.Ioo (-δ) (1+δ), A u 0 = γ u)
    (hγO : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) O)
    (t : ℝ) (ht : t ∈ Set.Ioo a b)
    (hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1, actualSpeedSq (h t) γ u = d^2) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ e.source) →
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 3 γ (Set.Ioo (-δ) (1+δ)) →
    -σ*(2*n : ℕ)*K*d^2 ≤
      deriv (fun s => fieldPathEnergy (h s) (fun u => A u (e.symm (γ 1)))) t := by
  letI := manifold_realSmooth M
  intro hA hγ
  let J := Set.Ioo (-δ) (1+δ)
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ J := by intro u hu; constructor <;> linarith [hu.1,hu.2]
  have Hfam : MetricFamilySmooth h (Set.Ioo a b) := by
    intro c i j
    exact (hflow.1 c i j).mono (fun p hp => ⟨hp.1,⟨hp.2.1.le,hp.2.2.le⟩⟩)
  have Hdensity := fieldPathSpeedSq_time_contDiffOn_two h _ isOpen_Ioo Hfam γ J isOpen_Ioo hγ
  have H := fieldPathEnergy_time_deriv_lower h O a b σ K d hσ hflow γ hγO t ht
    (fun u hu => hcurv (γ u) (hγO hu) t ⟨ht.1.le,ht.2.le⟩)
    (fun u hu => by rw [fieldPathSpeed_sq]; exact hspeed u hu)
    (Set.Ioo a b) J isOpen_Ioo isOpen_Ioo ht hunit (Hdensity.of_le (by norm_num))
  have hinvy : e.symm (γ 1) = 0 := by rw [← he0]; exact e.left_inv h0
  have Hfiber := (endpointVariation_fiber_contMDiffOn_three e A J hA 0 h0).of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)
  have HE : (fun s => fieldPathEnergy (h s) (fun u => A u (e.symm (γ 1)))) =
      (fun s => fieldPathEnergy (h s) γ) := by
    funext s
    rw [hinvy]
    exact fieldPathEnergy_congr_on_open (h s) (fun u => A u 0) γ J isOpen_Ioo hunit hA0 Hfiber
      (hγ.of_le (by norm_num))
  rw [HE]
  exact H

end Yau.LeafProofs.L23Aux
