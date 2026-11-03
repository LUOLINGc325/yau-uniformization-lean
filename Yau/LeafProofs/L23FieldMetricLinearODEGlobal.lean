import Yau.LeafProofs.L23FieldMetricLinearODESplice

/-! Finite actual fundamental-solution steps solve a C2 linear equation across the whole unit interval. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace Yau.LeafProofs.L23Aux
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
set_option maxHeartbeats 1200000

theorem exists_unit_fundamental_solution
    (A : ℝ → E →L[ℝ] E) (J : Set ℝ) (hJ : IsOpen J) (hA : ContDiffOn ℝ 2 A J)
    (hunit : Set.Icc (0 : ℝ) 1 ⊆ J) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W : ℝ → E →L[ℝ] E,
      W 0 = ContinuousLinearMap.id ℝ E ∧ ContDiffOn ℝ 3 W (Set.Ioo (-δ) (1+δ)) ∧
      ∀ t ∈ Set.Ioo (-δ) (1+δ), t ∈ J ∧ HasDerivAt W ((A t).comp (W t)) t := by
  obtain ⟨ε,hε,hfamily⟩ := exists_uniform_fundamental_solution A J hJ hA hunit
  obtain ⟨N,hN⟩ := exists_nat_gt (1/ε)
  let K := N+1
  have hK : (0 : ℝ) < K := by dsimp [K]; positivity
  let Δ : ℝ := 1/K
  have hΔ : 0 < Δ := div_pos zero_lt_one hK
  have hΔε : Δ < ε := by
    have H := (div_lt_iff₀ hε).mp hN
    apply (div_lt_iff₀ hK).mpr
    dsimp only [K]
    push_cast
    nlinarith
  have hKΔ : (K : ℝ)*Δ = 1 := by dsimp only [Δ]; field_simp [hK.ne']
  have hex : ∀ j : ℕ, j ≤ K → ∃ δ : ℝ, 0 < δ ∧ ∃ W : ℝ → E →L[ℝ] E,
      W 0 = ContinuousLinearMap.id ℝ E ∧
      ContDiffOn ℝ 3 W (Set.Ioo (-δ) ((j : ℝ)*Δ+δ)) ∧
      ∀ t ∈ Set.Ioo (-δ) ((j : ℝ)*Δ+δ), t ∈ J ∧ HasDerivAt W ((A t).comp (W t)) t := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨W,hW₀,hW,hsol⟩ := hfamily 0 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
      refine ⟨ε,hε,W,hW₀,?_,?_⟩
      · simpa only [Nat.cast_zero,zero_mul,zero_add] using hW
      · simpa only [Nat.cast_zero,zero_mul,zero_add] using hsol
    | succ j ih =>
      intro hj
      obtain ⟨δl,hδl,Wl,hWl₀,hWl,hsolL⟩ := ih (Nat.le_of_succ_le hj)
      let T : ℝ := (j : ℝ)*Δ
      have hTunit : T ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨mul_nonneg (Nat.cast_nonneg _) hΔ.le,?_⟩
        have Hj : (j : ℝ) ≤ K := by exact_mod_cast (Nat.le_of_succ_le hj)
        exact (mul_le_mul_of_nonneg_right Hj hΔ.le).trans_eq hKΔ
      obtain ⟨Z,hZ₀,hZ,hsolZ⟩ := hfamily T hTunit
      let Wr : ℝ → E →L[ℝ] E := fun t => (Z (t-T)).comp (Wl T)
      have hsolR (t : ℝ) (ht : t ∈ Set.Ioo (T-ε) (T+ε)) : HasDerivAt Wr ((A t).comp (Wr t)) t := by
        have hu : t-T ∈ Set.Ioo (-ε) ε := ⟨by linarith [ht.1],by linarith [ht.2]⟩
        have HD := HasDerivAt.comp_sub_const t T (hsolZ (t-T) hu).2
        have Htime : T+(t-T) = t := by ring
        rw [Htime] at HD
        have H := HD.clm_comp (hasDerivAt_const t (Wl T))
        simpa only [ContinuousLinearMap.comp_zero,add_zero,ContinuousLinearMap.comp_assoc] using H
      have hTleft : T ∈ Set.Ioo (-δl) ((j : ℝ)*Δ+δl) := by
        dsimp only [T]
        constructor <;> linarith [hTunit.1]
      have hTright : T ∈ Set.Ioo (T-ε) (T+ε) := by constructor <;> linarith
      have hmatch : Wl T = Wr T := by simp only [Wr,sub_self,hZ₀,ContinuousLinearMap.id_comp]
      have hsolSplice := linearODE_splice_hasDerivAt A Wl Wr (-δl) ((j : ℝ)*Δ+δl)
        (T-ε) (T+ε) T (fun t ht => (hsolL t ht).2) hsolR hTleft hTright hmatch
      let δ := min δl ((ε-Δ)/2)
      have hδ : 0 < δ := lt_min hδl (half_pos (sub_pos.mpr hΔε))
      have hδl' : δ ≤ δl := min_le_left _ _
      have hδr' : δ ≤ (ε-Δ)/2 := min_le_right _ _
      let W : ℝ → E →L[ℝ] E := fun t => if t ≤ T then Wl t else Wr t
      let I := Set.Ioo (-δ) (((j+1 : ℕ) : ℝ)*Δ+δ)
      have hsub (t : ℝ) (ht : t ∈ I) : t ∈ Set.Ioo (-δl) (T+ε) := by
        have Hhi : t < ((j : ℝ)+1)*Δ+δ := by simpa only [I,Nat.cast_add,Nat.cast_one] using ht.2
        change -δl < t ∧ t < (j : ℝ)*Δ+ε
        constructor <;> linarith [ht.1]
      have hmaps (t : ℝ) (ht : t ∈ I) : t ∈ J := by
        by_cases htT : t ≤ T
        · apply (hsolL t ⟨(hsub t ht).1,by dsimp only [T] at htT; linarith⟩).1
        · have hu : t-T ∈ Set.Ioo (-ε) ε :=
            ⟨by linarith [not_le.mp htT],by linarith [(hsub t ht).2]⟩
          have H := (hsolZ (t-T) hu).1
          have Htime : T+(t-T) = t := by ring
          rwa [Htime] at H
      have hsol (t : ℝ) (ht : t ∈ I) : HasDerivAt W ((A t).comp (W t)) t := hsolSplice t (hsub t ht)
      refine ⟨δ,hδ,W,?_,linearODE_contDiffOn_three A W I isOpen_Ioo (hA.mono hmaps) hsol,?_⟩
      · simpa only [W,if_pos hTunit.1] using hWl₀
      · intro t ht
        exact ⟨hmaps t ht,hsol t ht⟩
  obtain ⟨δ,hδ,W,hW₀,hW,hsol⟩ := hex K le_rfl
  refine ⟨δ,hδ,W,hW₀,?_,?_⟩
  · simpa only [hKΔ] using hW
  · simpa only [hKΔ] using hsol

end Yau.LeafProofs.L23Aux
