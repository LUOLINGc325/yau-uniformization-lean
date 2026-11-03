import Yau.Proofs.F01ClosedWirtingerSmooth
import Yau.Proofs.F01ClosedRicciFamily
import Yau.Proofs.F01FieldHeatPenalty

/-! The actual native heat operator is continuous in time up to both
faces of a jointly smooth slab, so an interior inequality passes to its faces. -/
noncomputable section
open Set
open scoped ContDiff Matrix Manifold ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem smoothSpaceTime_levi_time_smooth {F : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hF : SmoothSpaceTime F I) (hI : UniqueDiffOn ℝ I)
    (x : M.Carrier) (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun t => levi (fun y => F y t) x i j) I := by
  have hl : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ =>
      leviC (fun z => F (chartInv x z) p.2) p.1 i j) (chartTarget x ×ˢ I) :=
    closed_slab_leviC_smooth
      (F := fun p : ComplexVector n × ℝ => F (chartInv x p.1) p.2)
      (isOpen_extChartAt_target (I := ComplexModel n) x) hI (hF x) i j
  have hp : ContDiffOn ℝ ∞ (fun t : ℝ => (chartPt x x, t)) I :=
    contDiffOn_const.prodMk contDiffOn_id
  have ht := hl.comp hp (fun t ht => ⟨mem_extChartAt_target x, ht⟩)
  apply ht.congr
  intro t _
  rfl

theorem fieldHeatWithin_time_continuous (h : ℝ → HermitianField M)
    {F : M.Carrier → ℝ → ℝ} {I : Set ℝ} (hh : MetricFamilySmooth h I)
    (hF : SmoothSpaceTime F I) (hI : UniqueDiffOn ℝ I) (x : M.Carrier) :
    ContinuousOn (fun t => fieldHeatWithin h I (fun s y => F y s) x t) I := by
  have hInv (i j : Fin n) : ContDiffOn ℝ ∞ (fun t => (gMat (h t) x)⁻¹ i j) I :=
    L12Aux.contDiffOn_matrix_inv (fun i j => metricFamily_gMat_time_smooth h hh x i j)
      (fun t ht => ((L12Aux.hMat_posDef (h t) x (chartPt x x)
        (mem_extChartAt_target x)).isUnit.map Matrix.detMonoidHom).ne_zero) i j
  have hLevi := smoothSpaceTime_levi_time_smooth hF hI x
  have hLap : ContDiffOn ℝ ∞ (fun t => laplacian (h t) (fun y => F y t) x) I := by
    change ContDiffOn ℝ ∞ (fun t =>
      (∑ i, ∑ j, (gMat (h t) x)⁻¹ i j * levi (fun y => F y t) x j i).re) I
    exact Complex.reCLM.contDiff.comp_contDiffOn (ContDiffOn.sum (fun i _ =>
      ContDiffOn.sum (fun j _ => (hInv i j).mul (hLevi j i))))
  exact ((smoothSpaceTime_time_slice hF x).continuousOn_derivWithin hI (by simp)).sub
    hLap.continuousOn

theorem continuous_closed_interval_nonpos_of_interior {F : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hF : ContinuousOn F (Icc a b))
    (hnonpos : ∀ t ∈ Ioo a b, F t ≤ 0) : ∀ t ∈ Icc a b, F t ≤ 0 := by
  have hclosed : IsClosed {t ∈ Icc a b | F t ≤ 0} :=
    isClosed_Icc.isClosed_le hF continuousOn_const
  have hsub : Ioo a b ⊆ {t ∈ Icc a b | F t ≤ 0} :=
    fun t ht => ⟨⟨ht.1.le, ht.2.le⟩, hnonpos t ht⟩
  have hc := closure_minimal hsub hclosed
  rw [closure_Ioo hab.ne] at hc
  exact fun t ht => (hc ht).2

end Yau.NodeProofs.F01Aux
