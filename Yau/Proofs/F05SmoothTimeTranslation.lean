import Yau.Proofs.F05ManifoldTimeOperations

/-! The actual smooth metric/datum and the original nonlinear equation
transport through positive time translation, with the exact one-sided
derivatives on arbitrary closed source and destination intervals. -/

open Set
open scoped ContDiff
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_smooth_spacetime_time_shift {I J : Set ℝ} (s : ℝ)
    (hMap : MapsTo (fun t : ℝ => t+s) J I) (p : M.Carrier → ℝ → ℝ)
    (hp : SmoothSpaceTime p I) : SmoothSpaceTime (F05ManifoldTimeShift s p) J := by
  intro x
  have hEmb : ContDiffOn ℝ ∞ (fun z : Point n => (z.1,z.2+s)) (chartTarget x ×ˢ J) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const)
  have hMapQ : MapsTo (fun z : Point n => (z.1,z.2+s)) (chartTarget x ×ˢ J) (chartTarget x ×ˢ I) :=
    fun z hz => ⟨hz.1,hMap hz.2⟩
  have hRaw := (hp x).comp hEmb hMapQ
  exact hRaw

theorem F05_smooth_metric_time_shift {I J : Set ℝ} (s : ℝ)
    (hMap : MapsTo (fun t : ℝ => t+s) J I) (h : ℝ → HermitianField M)
    (hh : MetricFamilySmooth h I) : MetricFamilySmooth (fun t => h (t+s)) J := by
  intro x a b
  have hEmb : ContDiffOn ℝ ∞ (fun z : Point n => (z.1,z.2+s)) (chartTarget x ×ˢ J) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const)
  have hMapQ : MapsTo (fun z : Point n => (z.1,z.2+s)) (chartTarget x ×ˢ J) (chartTarget x ×ˢ I) :=
    fun z hz => ⟨hz.1,hMap hz.2⟩
  have hRaw := (hh x a b).comp hEmb hMapQ
  exact hRaw

theorem F05_manifold_time_shift_equation {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) {s l r L R : ℝ}
    (hlr : l < r) (hMap : MapsTo (fun t : ℝ => t+s) (Icc l r) (Icc L R))
    (w : M.Carrier → ℝ → ℝ)
    (hw : ∀ i, C2 (cylinder (F05D A i) L R) (pull A i w))
    (hEq : ∀ x ∈ closure O, ∀ t ∈ Icc L R,
      derivWithin (w x) (Icc L R) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
        (1-Real.exp (-w x t))*scalarCurvature (h t) x) :
    ∀ x ∈ closure O, ∀ t ∈ Icc l r,
      derivWithin (F05ManifoldTimeShift s w x) (Icc l r) t =
        Real.exp (-F05ManifoldTimeShift s w x t)*
          laplacian (h (t+s)) (fun y => F05ManifoldTimeShift s w y t) x+
        (1-Real.exp (-F05ManifoldTimeShift s w x t))*scalarCurvature (h (t+s)) x := by
  intro x hx t ht
  obtain ⟨i,z,hz,hzx⟩ := F05_cover hA hx
  have hFiber : {a : ℝ | (z,a) ∈ cylinder (F05D A i) L R} = Icc L R := by
    ext a
    exact and_iff_right hz
  have hDiff : DifferentiableWithinAt ℝ (w x) (Icc L R) (t+s) := by
    have hAt := (hw i).2.2.2.2.2 (z,t+s) ⟨hz,hMap ht⟩
    simpa only [hFiber,pull,hzx] using hAt
  have hChain := hDiff.hasDerivWithinAt.comp t
    (((hasDerivAt_id t).add_const s).hasDerivWithinAt) hMap
  have hTime := hChain.derivWithin (uniqueDiffOn_Icc hlr t ht)
  have hTime' : derivWithin (F05ManifoldTimeShift s w x) (Icc l r) t =
      derivWithin (w x) (Icc L R) (t+s) := by
    change derivWithin (fun a => w x (a+s)) (Icc l r) t = derivWithin (w x) (Icc L R) (t+s)
    simpa only [Function.comp_def,id_eq,mul_one] using hTime
  exact hTime'.trans (hEq x hx (t+s) (hMap ht))

end Yau.Proofs.F05Aux
