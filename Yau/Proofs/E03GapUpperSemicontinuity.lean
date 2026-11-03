import Yau.Proofs.E03FixedGapRegularity
import Yau.Proofs.E03ChartSemicontinuity
import Yau.Proofs.E03ScalarAlgebra

/-! The actual nonnegative gap is USC across its zero initial face on each shorter interval. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem scalarGap_upperSemicontinuousOn (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (T : ℝ) (hT : 0 < T) (S : ℝ) (_hS : 0 < S) (hST : S < T) :
    UpperSemicontinuousOn (fun p : Pt X × ℝ => scalarGap X h T p.1 p.2)
      (univ ×ˢ Icc 0 S) := by
  apply chartwise_upperSemicontinuousOn
  intro c
  rintro ⟨z, t⟩ hp
  let C : Set (ComplexVector n × ℝ) := chartTarget c ×ˢ Icc 0 S
  by_cases ht0 : t = 0
  · subst t
    refine upperSemicontinuousWithinAt_of_continuous_majorant_at_zero
      (fun p : ComplexVector n × ℝ => scalarGap X h T (chartInv c p.1) p.2)
      (fun p : ComplexVector n × ℝ => ρ (chartInv c p.1) p.2) C (z, 0) ?_ ?_ ?_ ?_
    · exact scalarGap_zero h T (chartInv c z)
    · exact Yau.F04Proof.rho_initial o h U P ρ hloc (chartInv c z)
    · have hr : ContDiffOn ℝ ∞
          (fun p : ComplexVector n × ℝ => ρ (chartInv c p.1) p.2) C :=
        (hloc.2.2.2.1 c).mono (fun p hp => ⟨hp.1, hp.2.1⟩)
      exact hr.continuousOn (z, 0) hp
    · have hmem : ∀ᶠ p in 𝓝[C] (z, 0), p ∈ C := self_mem_nhdsWithin
      exact hmem.mono (fun p hp =>
        (scalarGap_bounds o h U P ρ hloc hopt T hT S hST (chartInv c p.1) p.2 hp.2).2)
  · have hpos : 0 < t := lt_of_le_of_ne hp.2.1 (Ne.symm ht0)
    have htime : t ∈ Ioo 0 T := ⟨hpos, hp.2.2.trans_lt hST⟩
    intro a ha
    have he := scalarGap_fixed_chart h ρ hopt T hT c z t hp.1 htime
    have hcut : volumeGap X h T c z t < a := by simpa only [he] using ha
    have hv : ∀ᶠ p in 𝓝[chartTarget c ×ˢ Ioo 0 T] (z, t),
        volumeGap X h T c p.1 p.2 < a :=
      volumeGap_upperSemicontinuousOn o h U P ρ hloc hopt c T hT (z, t) ⟨hp.1, htime⟩ a hcut
    have hopen : IsOpen (chartTarget c ×ˢ Ioo 0 T) :=
      (isOpen_extChartAt_target (I := ComplexModel n) c).prod isOpen_Ioo
    rw [nhdsWithin_eq_nhds.mpr (hopen.mem_nhds ⟨hp.1, htime⟩)] at hv
    have htnear : ∀ᶠ p : ComplexVector n × ℝ in 𝓝 (z, t), 0 < p.2 :=
      continuousAt_snd.eventually (Ioi_mem_nhds hpos)
    have hmem : ∀ᶠ p in 𝓝[C] (z, t), p ∈ C := self_mem_nhdsWithin
    filter_upwards [hv.filter_mono nhdsWithin_le_nhds,
      htnear.filter_mono nhdsWithin_le_nhds, hmem] with p hcut hpos hp
    rw [scalarGap_fixed_chart h ρ hopt T hT c p.1 p.2 hp.1
      ⟨hpos, hp.2.2.trans_lt hST⟩]
    exact hcut

end Yau.NodeProofs.E03Aux
