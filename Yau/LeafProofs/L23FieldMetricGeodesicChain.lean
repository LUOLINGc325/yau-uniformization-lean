import Yau.LeafProofs.L23FieldMetricGeodesicSplice

/-! Finite chains of genuine unit geodesics with matching phases glue smoothly. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 1200000

def unitGeodesicChain {α : Type*} : (N : ℕ) → (Fin (N+1) → ℝ → α) → ℝ → α
  | 0,γ => γ 0
  | N+1,γ => fun u => if u ≤ 1 then γ 0 u else unitGeodesicChain N (fun i => γ i.succ) (u-1)

theorem unitGeodesicChain_eventuallyEq_first {α : Type*} (N : ℕ) (γ : Fin (N+1) → ℝ → α) :
    unitGeodesicChain N γ =ᶠ[𝓝 (0 : ℝ)] γ 0 := by
  cases N with
  | zero => exact EventuallyEq.rfl
  | succ N =>
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with u hu
    have Hu : u < 1 := hu
    simp [unitGeodesicChain,Hu.le]

theorem fieldGeodesicOn_mono (h : HermitianField M) (γ : ℝ → M.Carrier)
    {I J : Set ℝ} (hγ : FieldGeodesicOn h γ J) (hIJ : I ⊆ J) : FieldGeodesicOn h γ I :=
  ⟨hγ.1.mono hIJ,fun c u hu hc => hγ.2 c u (hIJ hu) hc⟩

theorem unitGeodesicChain_geodesic
    (h : HermitianField M) (hh : MetricSmooth h) (O : Set M.Carrier) (N : ℕ)
    (ε : Fin (N+1) → ℝ) (γ : Fin (N+1) → ℝ → M.Carrier)
    (hdata : ∀ i, 0 < ε i ∧ FieldGeodesicOn h (γ i) (Set.Ioo (-ε i) (1+ε i)) ∧
      Set.MapsTo (γ i) (Set.Icc (0 : ℝ) 1) O)
    (hmatch : ∀ j : Fin N, γ j.castSucc 1 = γ j.succ 0 ∧
      geoChartState (γ j.castSucc) (γ j.castSucc 1) 1 =
        geoChartState (γ j.succ) (γ j.castSucc 1) 0) :
    ∃ δ : ℝ, 0 < δ ∧
      FieldGeodesicOn h (unitGeodesicChain N γ) (Set.Ioo (-δ) ((N+1 : ℕ)+δ)) ∧
      Set.MapsTo (unitGeodesicChain N γ) (Set.Icc (0 : ℝ) (N+1 : ℕ)) O ∧
      ∀ (i : Fin (N+1)) (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 →
        unitGeodesicChain N γ =ᶠ[𝓝 ((i.val : ℝ)+t)] (fun u => γ i (u-i.val)) := by
  induction N with
  | zero =>
    refine ⟨ε 0,(hdata 0).1,?_,?_,?_⟩
    · simpa only [unitGeodesicChain,Nat.zero_add,Nat.cast_one] using (hdata 0).2.1
    · simpa only [unitGeodesicChain,Nat.zero_add,Nat.cast_one] using (hdata 0).2.2
    · intro i t ht
      have hi : i = 0 := by apply Fin.ext; have Hi := i.isLt; simp only [Fin.val_zero]; omega
      subst i
      simpa only [unitGeodesicChain,Fin.val_zero,Nat.cast_zero,zero_add,sub_zero] using
        (EventuallyEq.rfl : γ 0 =ᶠ[𝓝 t] γ 0)
  | succ N ih =>
    let εtail : Fin (N+1) → ℝ := fun i => ε i.succ
    let γtail : Fin (N+1) → ℝ → M.Carrier := fun i => γ i.succ
    obtain ⟨δtail,hδtail,hGeoTail,hMapTail,hEqTail⟩ := ih εtail γtail
      (fun i => hdata i.succ) (fun j => hmatch j.succ)
    let Γtail := unitGeodesicChain N γtail
    let g : ℝ → M.Carrier := fun u => Γtail (u-1)
    have hGeoG : FieldGeodesicOn h g (Set.Ioo (1-δtail) ((N+2 : ℕ)+δtail)) := by
      apply fieldGeodesicOn_mono h g (fieldGeodesicOn_shift h Γtail _ hGeoTail 1)
      intro u hu
      change -δtail < u-1 ∧ u-1 < (N+1 : ℕ)+δtail
      push_cast at hu ⊢
      constructor <;> linarith [hu.1,hu.2]
    have hfirst := unitGeodesicChain_eventuallyEq_first N γtail
    have hfirst₀ : Γtail 0 = γ (Fin.succ (0 : Fin (N+1))) 0 := hfirst.self_of_nhds
    have hM := hmatch (0 : Fin (N+1))
    have hg₁ : g 1 = γ 0 1 := by
      change Γtail (1-1) = γ 0 1
      rw [sub_self,hfirst₀]
      exact hM.1.symm
    have hphaseG : geoChartState g (γ 0 1) 1 = geoChartState (γ (Fin.succ (0 : Fin (N+1)))) (γ 0 1) 0 := by
      rw [geoChartState_shift,sub_self]
      exact geoChartState_congr_eventuallyEq Γtail _ _ 0 hfirst
    have hphase : geoChartState (γ 0) (γ 0 1) 1 = geoChartState g (γ 0 1) 1 :=
      hM.2.trans hphaseG.symm
    have hT₀ : (1 : ℝ) ∈ Set.Ioo (-ε 0) (1+ε 0) := by constructor <;> linarith [(hdata 0).1]
    have hT₁ : (1 : ℝ) ∈ Set.Ioo (1-δtail) ((N+2 : ℕ)+δtail) := by
      push_cast
      constructor <;> linarith
    have hsrc₀ : γ 0 1 ∈ (extChartAt (ComplexModel n) (γ 0 1)).source := mem_extChartAt_source _
    have hsrc₁ : g 1 ∈ (extChartAt (ComplexModel n) (γ 0 1)).source := by rw [hg₁]; exact hsrc₀
    have hGeo := fieldGeodesicOn_splice h hh (γ 0) g (-ε 0) (1+ε 0) (1-δtail)
      ((N+2 : ℕ)+δtail) 1 (hdata 0).2.1 hGeoG hT₀ hT₁ (γ 0 1) hsrc₀ hsrc₁ hphase
    have heq := fieldGeodesics_eventuallyEq_of_same_chart_phase h hh (γ 0 1) (γ 0) g
      isOpen_Ioo isOpen_Ioo (hdata 0).2.1 hGeoG 1 hT₀ hT₁ hsrc₀ hsrc₁ hphase
    let δ := min (ε 0) δtail
    have hδ : 0 < δ := lt_min (hdata 0).1 hδtail
    have hδ₀ : δ ≤ ε 0 := min_le_left _ _
    have hδ₁ : δ ≤ δtail := min_le_right _ _
    refine ⟨δ,hδ,?_,?_,?_⟩
    · apply fieldGeodesicOn_mono h (unitGeodesicChain (N+1) γ) hGeo
      intro u hu
      constructor <;> linarith [hu.1,hu.2]
    · intro u hu
      by_cases hu₁ : u ≤ 1
      · change (if u ≤ 1 then γ 0 u else Γtail (u-1)) ∈ O
        rw [if_pos hu₁]
        exact (hdata 0).2.2 ⟨hu.1,hu₁⟩
      · change (if u ≤ 1 then γ 0 u else Γtail (u-1)) ∈ O
        rw [if_neg hu₁]
        apply hMapTail
        push_cast at hu ⊢
        exact ⟨by linarith [not_le.mp hu₁],by linarith [hu.2]⟩
    · intro i t ht
      refine Fin.cases ?_ (fun k => ?_) i
      · have Hnear : unitGeodesicChain (N+1) γ =ᶠ[𝓝 t] γ 0 := by
          by_cases ht₁ : t < 1
          · filter_upwards [Iio_mem_nhds ht₁] with u hu
            exact if_pos hu.le
          · have htEq : t = 1 := le_antisymm ht.2 (le_of_not_gt ht₁)
            subst t
            exact splice_eventuallyEq_left (γ 0) g 1 heq
        simpa only [Fin.val_zero,Nat.cast_zero,zero_add,sub_zero] using Hnear
      · let s : ℝ := (k.succ.val : ℝ)+t
        have hs : 1 ≤ s := by
          have Hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg k.val
          dsimp only [s]
          simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
          linarith [ht.1]
        have Hnear : unitGeodesicChain (N+1) γ =ᶠ[𝓝 s] g := by
          by_cases hs₁ : 1 < s
          · filter_upwards [Ioi_mem_nhds hs₁] with u hu
            exact if_neg (not_le.mpr hu)
          · have hsEq : s = 1 := le_antisymm (le_of_not_gt hs₁) hs
            rw [hsEq]
            exact (splice_eventuallyEq_left (γ 0) g 1 heq).trans heq
        have hsShift : s-1 = (k.val : ℝ)+t := by
          dsimp only [s]
          simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
          ring
        have HT : Γtail =ᶠ[𝓝 (s-1)] (fun u => γtail k (u-k.val)) := by
          rw [hsShift]
          exact hEqTail k t ht
        have Hmap := (continuousAt_id.sub continuousAt_const : ContinuousAt (fun u : ℝ => u-1) s).eventually HT
        filter_upwards [Hnear,Hmap] with u hu htu
        calc
          _ = Γtail (u-1) := hu
          _ = γtail k ((u-1)-k.val) := htu
          _ = γ k.succ (u-k.succ.val) := by
            dsimp only [γtail]
            congr 1
            simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
            ring

end Yau.LeafProofs.L23Aux
