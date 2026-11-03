import Yau.Proofs.C02ODEUnique

/-! The solution of the tangent-lift equation is identified with the actual
first variation on a common neighborhood, using the two ODEs and uniqueness. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
universe u
namespace Yau.Blueprint.C02Proof
open Yau.LeafProofs.L12Aux

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : E → E} {z₀ : E} {U : Set E}

theorem localFlow_pair_eq_tangentLift
    (hF : ContDiffAt ℝ 2 F z₀)
    (d : LocalVariationalFlow F z₀ U)
    (e : LocalVariationalFlow (odeVariationField F)
      (z₀, ContinuousLinearMap.id ℝ E) univ) :
    (fun p : E × ℝ => (d.solution p.1 p.2, d.variation p.1 p.2)) =ᶠ[𝓝 (z₀, 0)]
      (fun p : E × ℝ => e.solution (p.1, ContinuousLinearMap.id ℝ E) p.2) := by
  let κ : E × ℝ → (E × (E →L[ℝ] E)) × ℝ :=
    fun p => ((p.1, ContinuousLinearMap.id ℝ E), p.2)
  have hκ : ContinuousAt κ (z₀, 0) := by fun_prop
  let N := d.domain ∩ κ ⁻¹' e.domain
  have hN : N ∈ 𝓝 (z₀, 0) :=
    Filter.inter_mem d.domain_mem_nhds (hκ.preimage_mem_nhds e.domain_mem_nhds)
  apply eventuallyEq_ODE_families (N := N) (F := odeVariationField F)
    (f := fun z t => (d.solution z t, d.variation z t))
    (g := fun z t => e.solution (z, ContinuousLinearMap.id ℝ E) t) (a₀ := z₀)
  · simpa only [d.solution_center, d.variation_center] using odeVariationField_contDiffAt hF
  · exact d.solution_continuousAt.prodMk d.variation_continuousAt
  · have hc := e.solution_continuousAt.comp_of_eq hκ rfl
    convert hc using 1 <;> rfl
  · exact hN
  · intro z hz
    have hd := d.initial z hz.1.1
    have he := e.initial (z, ContinuousLinearMap.id ℝ E) hz.2.1
    exact (Prod.ext hd.1 hd.2).trans he.1.symm
  · intro p hp
    exact d.pair_equation hp.1.1 hp.1.2
  · intro p hp
    exact (e.equation (p.1, ContinuousLinearMap.id ℝ E) hp.2.1 p.2 hp.2.2).2.1

theorem localFlow_pair_contDiffAt_of_tangentLift (m : ℕ)
    (hF : ContDiffAt ℝ 2 F z₀)
    (d : LocalVariationalFlow F z₀ U)
    (e : LocalVariationalFlow (odeVariationField F)
      (z₀, ContinuousLinearMap.id ℝ E) univ)
    (he : ContDiffAt ℝ m (Function.uncurry e.solution)
      ((z₀, ContinuousLinearMap.id ℝ E), 0)) :
    ContDiffAt ℝ m (fun p : E × ℝ => (d.solution p.1 p.2, d.variation p.1 p.2))
      (z₀, 0) := by
  have hκ : ContDiffAt ℝ m
      (fun p : E × ℝ => ((p.1, ContinuousLinearMap.id ℝ E), p.2)) (z₀, 0) :=
    (contDiffAt_fst.prodMk contDiffAt_const).prodMk contDiffAt_snd
  have hcomp : ContDiffAt ℝ m
      (fun p : E × ℝ => e.solution (p.1, ContinuousLinearMap.id ℝ E) p.2) (z₀, 0) :=
    by
      simpa only [Function.comp_def, Function.uncurry_apply_pair] using
        (ContDiffAt.comp (f := fun p : E × ℝ =>
          ((p.1, ContinuousLinearMap.id ℝ E), p.2))
          (g := Function.uncurry e.solution) (z₀, 0) he hκ)
  exact hcomp.congr_of_eventuallyEq (localFlow_pair_eq_tangentLift hF d e)

theorem localFlow_contDiffAt_succ_of_pair (m : ℕ)
    (hF : ContDiffAt ℝ ∞ F z₀)
    (d : LocalVariationalFlow F z₀ U)
    (hp : ContDiffAt ℝ m
      (fun p : E × ℝ => (d.solution p.1 p.2, d.variation p.1 p.2)) (z₀, 0)) :
    ContDiffAt ℝ (m + 1) (Function.uncurry d.solution) (z₀, 0) := by
  have hφ : ContDiffAt ℝ m (Function.uncurry d.solution) (z₀, 0) := hp.fst
  have hV : ContDiffAt ℝ m (Function.uncurry d.variation) (z₀, 0) := hp.snd
  have hFm : ContDiffAt ℝ m F (d.solution z₀ 0) := by
    rw [d.solution_center]
    exact hF.of_le (by simp)
  have hb : ContDiffAt ℝ m (fun p : E × ℝ => F (d.solution p.1 p.2)) (z₀, 0) :=
    hFm.comp (z₀, 0) hφ
  have hSpan : ContDiffAt ℝ m
      (fun p : E × ℝ => ContinuousLinearMap.toSpanSingleton ℝ (F (d.solution p.1 p.2)))
      (z₀, 0) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).contDiff.contDiffAt.comp (z₀, 0) hb
  let J : E × ℝ → (E × ℝ) →L[ℝ] E := fun p =>
    (d.variation p.1 p.2).coprod (ContinuousLinearMap.toSpanSingleton ℝ (F (d.solution p.1 p.2)))
  have hJ : ContDiffAt ℝ m J (z₀, 0) := by
    exact (hV.clm_comp (contDiffAt_const (c := ContinuousLinearMap.fst ℝ E ℝ))).add
      (hSpan.clm_comp (contDiffAt_const (c := ContinuousLinearMap.snd ℝ E ℝ)))
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  exact ⟨J, ⟨d.domain, d.domain_mem_nhds, d.joint_derivative⟩, hJ⟩

end Yau.Blueprint.C02Proof
