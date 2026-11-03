import Yau.LeafProofs.L23FieldMetricGaussVariation

/-! The genuine local endpoint differential satisfies the Gauss pairing. -/
noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem chartGeodesicFamily_gauss
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (B : Set (ComplexVector n)) (hB : IsOpen B) {ρ ε : ℝ} (hε : 0 < ε)
    (η : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (hη : ContDiffOn ℝ 2 (Function.uncurry η)
      ((B ×ˢ Metric.ball (0 : ComplexVector n) ρ) ×ˢ Set.Ioo (-ε) (1+ε)))
    (hi : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ, η p 0 = p)
    (hs : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ,
      ∀ u ∈ Set.Ioo (-ε) (1+ε), (η p u).1 ∈ chartTarget c ∧
        HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u)
    {z v : ComplexVector n} (hz : z ∈ B) (hv : v ∈ Metric.ball (0 : ComplexVector n) ρ)
    (w : ComplexVector n) :
    realMetricInChart h c (η (z,v) 1).1 (η (z,v) 1).2
      (fderiv ℝ (fun b => (η (z,b) 1).1) v w) = realMetricInChart h c z v w := by
  have hlin : ContinuousAt (fun r : ℝ => v+r • w) 0 := by fun_prop
  have hnear : ∀ᶠ r in 𝓝 (0 : ℝ), v+r • w ∈ Metric.ball (0 : ComplexVector n) ρ :=
    hlin.preimage_mem_nhds (by simpa using Metric.isOpen_ball.mem_nhds hv)
  obtain ⟨a,ha,hasub⟩ := Metric.mem_nhds_iff.mp hnear
  have hline (r : ℝ) (hr : r ∈ Set.Ioo (-a) a) :
      (z,v+r • w) ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ := by
    refine ⟨hz,hasub ?_⟩
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt] using
      (show -a < r ∧ r < a from hr)
  let ζ : ℝ × ℝ → ComplexVector n × ComplexVector n := fun p => η (z,v+p.1 • w) p.2
  have hmap : ContDiff ℝ 2 (fun p : ℝ × ℝ => ((z,v+p.1 • w),p.2)) := by fun_prop
  have hζ : ContDiffOn ℝ 2 ζ (Set.Ioo (-a) a ×ˢ Set.Ioo (-ε) (1+ε)) :=
    hη.comp hmap.contDiffOn (fun p hp => ⟨hline p.1 hp.1,hp.2⟩)
  have H := chartGeodesic_variation_gauss h hh c ζ z v w ha hε hζ
    (fun r hr => hi _ (hline r hr))
    (fun r hr u hu => hs _ (hline r hr) u hu)
    (t := 1) (by constructor <;> linarith)
  have h₁ : (1 : ℝ) ∈ Set.Ioo (-ε) (1+ε) := by constructor <;> linarith
  have hdiff : DifferentiableAt ℝ (fun b => (η (z,b) 1).1) v := by
    have hEmbed : ContDiffAt ℝ 2 (fun b : ComplexVector n => ((z,b),(1 : ℝ))) v := by fun_prop
    have hP : ((z,v),(1 : ℝ)) ∈
        (B ×ˢ Metric.ball (0 : ComplexVector n) ρ) ×ˢ Set.Ioo (-ε) (1+ε) := ⟨⟨hz,hv⟩,h₁⟩
    have Hη : ContDiffAt ℝ 2 (Function.uncurry η) ((z,v),(1 : ℝ)) :=
      hη.contDiffAt (((hB.prod Metric.isOpen_ball).prod isOpen_Ioo).mem_nhds hP)
    exact ((Hη.comp v hEmbed).fst).differentiableAt (by norm_num)
  have hvel : HasDerivAt (fun r : ℝ => v+r • w) w 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v using 1 <;> simp
  have HF : HasFDerivAt (fun b => (η (z,b) 1).1)
      (fderiv ℝ (fun b => (η (z,b) 1).1) v) (v+(0 : ℝ) • w) := by
    simpa only [zero_smul,add_zero] using hdiff.hasFDerivAt
  have Hd := HF.comp_hasDerivAt 0 hvel
  have hderiv : deriv (fun r => (ζ (r,1)).1) 0 =
      fderiv ℝ (fun b => (η (z,b) 1).1) v w := by
    simpa only [Function.comp_def,ζ] using Hd.deriv
  rw [hderiv] at H
  simpa only [ζ,zero_smul,add_zero,one_mul] using H

end Yau.LeafProofs.L23Aux
