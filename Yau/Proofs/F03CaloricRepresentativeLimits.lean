import Yau.Proofs.F03CaloricTensorBound

/-! Strong graph convergence controls actual pointwise values and all mixed jets. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.Proofs.F03Aux
open Yau Parabolic ParabolicCandidates
variable {d : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

section
variable (hd : 0 < d) (O : Set (Space d)) (l r lam upper : ℝ) (hO : IsOpen O) (hlr : l < r)
  (a : Point d → Mat d) (b : Point d → RIdx d → ℝ)
  (hAB : SmoothCoefficients (O ×ˢ Ioo l r) a b) (hEll : Elliptic (O ×ˢ Ioo l r) a lam upper)

theorem caloricRepresentative_sub
    (e f : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB) :
    EqOn (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll (e-f))
      (fun p => caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e p-
        caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll f p) (O ×ˢ Ioo l r) := by
  have he := caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll e
  have hf := caloricRepresentative_spec hd O l r lam upper hO hlr a b hAB hEll f
  apply caloricRepresentative_eqOn_of_ae hd O l r lam upper hO hlr a b hAB hEll (e-f)
    _ (he.1.continuousOn.sub hf.1.continuousOn)
  filter_upwards [Lp.coeFn_sub e.val.1 f.val.1,he.2.1,hf.2.1] with p hp hpe hpf
  change (e.val.1-f.val.1) p=_
  rw [hp,Pi.sub_apply,hpe,hpf]
  rfl

theorem caloricRepresentative_tendsto_at
    (es : ℕ → CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB)
    (e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB)
    (hLim : Tendsto es atTop (𝓝 e)) (p : Point d) (hp : p ∈ O ×ˢ Ioo l r) :
    Tendsto (fun j => caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll (es j) p) atTop
      (𝓝 (caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e p)) := by
  obtain ⟨W,hW,hpW,hWD,hWc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    (hO.prod isOpen_Ioo) (singleton_subset_iff.mpr hp)
  let L : Set (Point d) := closure W
  have hLc : IsCompact L := hWc
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hLc
  letI : IsFiniteMeasure (volume.comap ((↑) : L → Point d)) :=
    comap_subtype_isFiniteMeasure_of_measure_lt_top volume L hLc.measurableSet hLc.measure_lt_top
  have hreg : L=closure (interior L) :=
    subset_antisymm (closure_mono hW.subset_interior_closure) (closure_minimal interior_subset isClosed_closure)
  let T := caloricCompactJet hd O l r lam upper hO hlr a b hAB hEll L hWD []
  have hT : Continuous T := caloricCompactJet_continuous hd O l r lam upper hO hlr a b hAB hEll
    L hLc hreg hWD []
  have hpL : p ∈ L := subset_closure (hpW (mem_singleton p))
  have hEval : Continuous (fun q : C(L,ℝ) => q ⟨p,hpL⟩) := continuous_eval_const (⟨p,hpL⟩ : L)
  exact (hEval.tendsto (T e)).comp ((hT.tendsto e).comp hLim)

theorem caloricRepresentative_compact_tensor_sub_limit
    (es : ℕ → CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB)
    (e : CaloricSpace (O ×ˢ Ioo l r) (hO.prod isOpen_Ioo) a b hAB)
    (hLim : Tendsto es atTop (𝓝 e))
    (K : Set (Point d)) (hK : IsCompact K) (hKD : K ⊆ O ×ˢ Ioo l r) (m : ℕ)
    (η : ℝ) (hη : 0 < η) :
    ∃ J : ℕ,∀ j, J ≤ j → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ m (fun q =>
        caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll (es j) q-
          caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e q) p‖ < η := by
  obtain ⟨W,hW,hKW,hWD,hWc⟩ := exists_open_between_and_isCompact_closure hK (hO.prod isOpen_Ioo) hKD
  let L : Set (Point d) := closure W
  have hLc : IsCompact L := hWc
  letI : CompactSpace L := isCompact_iff_compactSpace.mp hLc
  letI : IsFiniteMeasure (volume.comap ((↑) : L → Point d)) :=
    comap_subtype_isFiniteMeasure_of_measure_lt_top volume L hLc.measurableSet hLc.measure_lt_top
  have hreg : L=closure (interior L) :=
    subset_antisymm (closure_mono hW.subset_interior_closure) (closure_minimal interior_subset isClosed_closure)
  obtain ⟨C,hC,hBound⟩ := caloricRepresentative_compact_tensor_bound hd O l r lam upper hO hlr a b hAB hEll
    L hLc hreg hWD m
  have hn : Tendsto (fun j => ‖es j-e‖) atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hLim
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (hn.eventually (gt_mem_nhds (div_pos hη hC)))
  refine ⟨J,fun j hj p hp => ?_⟩
  have hgerm : caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll (es j-e) =ᶠ[𝓝 p]
      (fun q => caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll (es j) q-
        caloricRepresentative hd O l r lam upper hO hlr a b hAB hEll e q) := by
    filter_upwards [(hO.prod isOpen_Ioo).mem_nhds (hKD hp)] with q hq
    exact caloricRepresentative_sub hd O l r lam upper hO hlr a b hAB hEll (es j) e hq
  rw [← (hgerm.iteratedFDeriv ℝ m).eq_of_nhds]
  calc
    _ ≤ C*‖es j-e‖ := hBound _ p (subset_closure (hKW hp))
    _ < C*(η/C) := mul_lt_mul_of_pos_left (hJ j hj) hC
    _ = η := by field_simp
end
end Yau.Proofs.F03Aux
