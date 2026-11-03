import Yau.Proofs.P03Convolution

open scoped Topology Convolution
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

theorem continuous_compact_norm_bound {k : ComplexVector n → ℂ}
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖k x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (hkc.isCompact_range hk).isBounded.exists_norm_le
  exact ⟨B, (norm_nonneg (k 0)).trans (hB _ (Set.mem_range_self 0)),
    fun x => hB _ (Set.mem_range_self x)⟩

theorem cmulConv_comm (f g : ComplexVector n → ℂ) : cmulConv f g = cmulConv g f := by
  apply convolution_symm
  ext a b
  exact mul_comm b a

/-- Associativity is used only after proving the actual two-variable
integrand integrable by a bounded compact kernel and two L¹ factors. -/
theorem cmulConv_assoc {f g k : ComplexVector n → ℂ}
    (hf : Integrable f volume) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hk : Continuous k) (hkc : HasCompactSupport k) :
    cmulConv (cmulConv f g) k = cmulConv f (cmulConv g k) := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  have hgi : Integrable g volume := hg.integrable_of_hasCompactSupport hgc
  have hfg := hgc.convolutionExists_right L hf.locallyIntegrable hg
  have hgk := hkc.convolutionExists_right L hgi.locallyIntegrable hk
  obtain ⟨B, hB0, hB⟩ := continuous_compact_norm_bound hk hkc
  ext x₀
  have hi0 := hf.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hgi.norm
  have hm0 : AEStronglyMeasurable (fun p : ComplexVector n × ComplexVector n =>
      f p.2 * g (p.1 - p.2)) (volume.prod volume) :=
    hf.aestronglyMeasurable.convolution_integrand L hg.aestronglyMeasurable
  have hm1 : AEStronglyMeasurable (fun p : ComplexVector n × ComplexVector n =>
      k (x₀ - p.1)) (volume.prod volume) :=
    (hk.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun p : ComplexVector n × ComplexVector n =>
      f p.2 * (g (p.1 - p.2) * k (x₀ - p.1))) (volume.prod volume) := by
    exact (hm0.mul hm1).congr (Filter.Eventually.of_forall
      fun p : ComplexVector n × ComplexVector n => mul_assoc (f p.2) (g (p.1 - p.2)) (k (x₀ - p.1)))
  have hi : Integrable (fun p : ComplexVector n × ComplexVector n =>
      f p.2 * (g (p.1 - p.2) * k (x₀ - p.1))) (volume.prod volume) := by
    apply (hi0.const_mul B).mono' hm
    filter_upwards with p
    simp only [norm_mul]
    calc
      ‖f p.2‖ * (‖g (p.1 - p.2)‖ * ‖k (x₀ - p.1)‖) ≤
          ‖f p.2‖ * (‖g (p.1 - p.2)‖ * B) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)) (norm_nonneg _)
      _ = B * (‖f p.2‖ * ‖g (p.1 - p.2)‖) := by ring
  exact convolution_assoc' L L L L (fun a b c => mul_assoc a b c)
    (Filter.Eventually.of_forall hfg) (Filter.Eventually.of_forall hgk) hi

theorem smoothBy_commute {f : ComplexVector n → ℂ} {k l : ComplexVector n → ℝ}
    (hf : Integrable f volume) (hk : Continuous k) (hkc : HasCompactSupport k)
    (hl : Continuous l) (hlc : HasCompactSupport l) :
    smoothBy k (smoothBy l f) = smoothBy l (smoothBy k f) := by
  let kc : ComplexVector n → ℂ := fun x => (k x : ℂ)
  let lc : ComplexVector n → ℂ := fun x => (l x : ℂ)
  have hkc' : HasCompactSupport kc := hkc.comp_left (g := Complex.ofReal) (by simp)
  have hlc' : HasCompactSupport lc := hlc.comp_left (g := Complex.ofReal) (by simp)
  have hk' : Continuous kc := Complex.continuous_ofReal.comp hk
  have hl' : Continuous lc := Complex.continuous_ofReal.comp hl
  rw [smoothBy_eq_cmulConv k (smoothBy l f), smoothBy_eq_cmulConv l f,
    smoothBy_eq_cmulConv l (smoothBy k f), smoothBy_eq_cmulConv k f]
  change cmulConv (cmulConv f lc) kc = cmulConv (cmulConv f kc) lc
  calc
    cmulConv (cmulConv f lc) kc = cmulConv f (cmulConv lc kc) :=
      cmulConv_assoc hf hl' hlc' hk' hkc'
    _ = cmulConv f (cmulConv kc lc) := by rw [cmulConv_comm lc kc]
    _ = cmulConv (cmulConv f kc) lc := (cmulConv_assoc hf hk' hkc' hl' hlc').symm

end Yau.NodeProofs.P03Aux
