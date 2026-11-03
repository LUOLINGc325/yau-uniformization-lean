import Yau.LeafProofs.L23FieldMetricLinearODE

/-! Compact time intervals give one genuine short fundamental-solution radius. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 600000

theorem exists_uniform_fundamental_solution
    (A : ℝ → E →L[ℝ] E) (J : Set ℝ) (hJ : IsOpen J) (hA : ContDiffOn ℝ 2 A J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ W : ℝ → E →L[ℝ] E,
      W 0 = ContinuousLinearMap.id ℝ E ∧ ContDiffOn ℝ 3 W (Set.Ioo (-ε) ε) ∧
      ∀ u ∈ Set.Ioo (-ε) ε, t+u ∈ J ∧ HasDerivAt W ((A (t+u)).comp (W u)) u := by
  classical
  let S := Set.Icc (0 : ℝ) 1
  have hex : ∀ t₀ : S, ∃ r : ℝ, 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Metric.ball t₀.val r, ∃ W : ℝ → E →L[ℝ] E,
        W 0 = ContinuousLinearMap.id ℝ E ∧ ContDiffOn ℝ 3 W (Set.Ioo (-ε) ε) ∧
        ∀ u ∈ Set.Ioo (-ε) ε, t+u ∈ J ∧ HasDerivAt W ((A (t+u)).comp (W u)) u :=
    fun t₀ => exists_local_fundamental_solution A J hJ hA t₀.val (hunit t₀.property)
  choose r hr ε hε hfamily using hex
  have hcover : S ⊆ ⋃ t₀ : S, Metric.ball t₀.val (r t₀) := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t,ht⟩,Metric.mem_ball_self (hr ⟨t,ht⟩)⟩
  obtain ⟨F,hF⟩ := isCompact_Icc.elim_finite_subcover (fun t₀ : S => Metric.ball t₀.val (r t₀))
    (fun _ => Metric.isOpen_ball) hcover
  have hFne : F.Nonempty := by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hF (show (0 : ℝ) ∈ S from ⟨le_rfl,zero_le_one⟩))
    obtain ⟨hiF,_⟩ := Set.mem_iUnion.mp hi
    exact ⟨i,hiF⟩
  have hImageNe : (F.image ε).Nonempty := hFne.image ε
  let εstar := (F.image ε).min' hImageNe
  have hεstar : 0 < εstar := by
    obtain ⟨i,hi,hieq⟩ := Finset.mem_image.mp ((F.image ε).min'_mem hImageNe)
    have H := hε i
    rw [hieq] at H
    exact H
  have hεle (i : S) (hi : i ∈ F) : εstar ≤ ε i :=
    Finset.min'_le (F.image ε) (ε i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  refine ⟨εstar,hεstar,?_⟩
  intro t ht
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hF ht)
  obtain ⟨hiF,hti⟩ := Set.mem_iUnion.mp hi
  obtain ⟨W,hW₀,hW,hsol⟩ := hfamily i t hti
  have hsub : Set.Ioo (-εstar) εstar ⊆ Set.Ioo (-ε i) (ε i) := by
    intro u hu
    exact ⟨(neg_le_neg (hεle i hiF)).trans_lt hu.1,hu.2.trans_le (hεle i hiF)⟩
  exact ⟨W,hW₀,hW.mono hsub,(fun u hu => hsol u (hsub hu))⟩

end Yau.LeafProofs.L23Aux
