import Yau.Proofs.G01RicciNormalization
import Yau.LeafProofs.L23TensorCalculus

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.G04Aux
open Yau Yau.Blueprint Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {M : ComplexManifold n}

theorem realRicciCoeff_center_raw (h : HermitianField M) (hs : MetricSmooth h)
    (hk : KahlerClosed h) (x : M.Carrier) (a b : RIdx n) :
    realRicciCoeff h x (chartPt x x) a b = 2 * G01Aux.rawReal (ricci h x) a b := by
  rw [L23Aux.realRicciCoeff_eq_realRicciMatrix h x (chartPt x x) (mem_extChartAt_target x),
    G01Aux.realRicciMatrix_eq_realification h hs hk x (chartPt x x) (mem_extChartAt_target x),
    G01Aux.hermitianRealification_eq]
  rfl

theorem flowReal : KahlerFlowRealNormalization := by
  intro n M g h hh
  refine ⟨hh.2.1, ?_⟩
  intro x _ t ht a b
  have hs := L23Aux.metricFamilySmooth_slice h hh.2.1 ht
  have hk := hh.2.2.1 t ht
  have hR := realRicciCoeff_center_raw (h t) hs hk x a b
  have hd := hh.2.2.2 x t ht a.1 b.1
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hd
  have hG (s : ℝ) : realMetricFn (h s) x (chartPt x x) a b =
      2 * G01Aux.rawReal (gMat (h s) x) a b := by
    exact congrArg (fun G : Matrix (RIdx n) (RIdx n) ℝ => G a b)
      (G01Aux.realMetricFn_eq_rawReal (h s) x (chartPt x x))
  simp_rw [hG]
  rw [hR]
  by_cases hab : a.2 = b.2
  · simpa [G01Aux.rawReal, hab, Function.comp_def] using hr.const_mul 2
  · by_cases ha : a.2 = 0
    · have hb : (0 : Fin 2) ≠ b.2 := fun he => hab (ha.trans he)
      simpa [G01Aux.rawReal, hab, ha, hb, Function.comp_def] using (hi.neg).const_mul 2
    · simpa [G01Aux.rawReal, hab, ha, Function.comp_def] using hi.const_mul 2

theorem metricFamilySmooth_twice (h : ℝ → HermitianField M)
    (hh : MetricFamilySmooth h (Set.Ici 0)) :
    MetricFamilySmooth (fun τ => h (2 * τ)) (Set.Ici 0) := by
  intro x a b
  have hc : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => (p.1, 2 * p.2))
      (chartTarget x ×ˢ Set.Ici 0) :=
    contDiffOn_fst.prodMk (contDiffOn_const.mul contDiffOn_snd)
  exact (hh x a b).comp hc (fun p hp => ⟨hp.1,
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (show 0 ≤ p.2 from hp.2)⟩)

theorem flowStandardTime : KahlerFlowStandardTimeNormalization := by
  intro n M g h hh
  have hreal := flowReal n M g h hh
  refine ⟨metricFamilySmooth_twice h hh.2.1, ?_⟩
  intro x hx τ hτ a b
  have ht : 2 * τ ∈ Set.Ici (0 : ℝ) :=
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (show 0 ≤ τ from hτ)
  have hm : Set.MapsTo (fun s : ℝ => 2 * s) (Set.Ici 0) (Set.Ici 0) :=
    fun s hs => mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (show 0 ≤ s from hs)
  have hl : HasDerivWithinAt (fun s : ℝ => 2 * s) 2 (Set.Ici 0) τ := by
    exact (hasDerivAt_const_mul (x := τ) (2 : ℝ)).hasDerivWithinAt
  have hd := (hreal.2 x hx (2 * τ) ht a b).comp τ hl hm
  convert hd using 1 <;> simp only [Function.comp_def] <;> ring

end Yau.NodeProofs.G04Aux
