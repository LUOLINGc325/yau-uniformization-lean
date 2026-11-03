import Yau.LeafProofs.L16ExpBoundaryCalculus
import Yau.LeafProofs.L16CompactCoefficientBounds

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryAux

open Yau.Parabolic Yau.ParabolicCandidates

theorem differentiableAt_d {n : ℕ} {f : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 2 f x) (j : Yau.RIdx n) :
    DifferentiableAt ℝ (fun y => d f y j) x :=
  ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const (Yau.realVec j))

/-- The flux is rewritten before differentiating; no derivative of 1/q occurs. -/
theorem log_flux_divergence {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {a : Space n → Mat n} {q : Space n → ℝ} {x : Space n} (hx : x ∈ O)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hq : ∀ y ∈ O, ContDiffAt ℝ 2 q y) (hpos : ∀ y ∈ O, q y ≠ 0)
    (i : Yau.RIdx n) :
    d (fun y => ∑ j, (a y i j/q y)*d q y j) x i =
      ∑ j, (d (fun y => a y i j) x i*d (fun y => Real.log (q y)) x j +
        a x i j*fderiv ℝ (fderiv ℝ (fun y => Real.log (q y))) x
          (Yau.realVec i) (Yau.realVec j)) := by
  have hlog := (hq x hx).log (hpos x hx)
  have heq : (fun y => ∑ j, (a y i j/q y)*d q y j) =ᶠ[𝓝 x]
      fun y => ∑ j, a y i j*d (fun z => Real.log (q z)) y j := by
    filter_upwards [hO.mem_nhds hx] with y hy
    apply Finset.sum_congr rfl
    intro j hj
    rw [d_log ((hq y hy).differentiableAt (by norm_num)) (hpos y hy)]
    ring
  have hd : d (fun y => ∑ j, (a y i j/q y)*d q y j) x i =
      d (fun y => ∑ j, a y i j*d (fun z => Real.log (q z)) y j) x i :=
    congrArg (fun L : Space n →L[ℝ] ℝ => L (Yau.realVec i)) heq.fderiv_eq
  rw [hd]
  rw [d_sum (f := fun j y => a y i j*d (fun z => Real.log (q z)) y j)
    (fun j => (ha i j).mul (differentiableAt_d hlog j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [d_mul (ha i j) (differentiableAt_d hlog j), d_d hlog]

theorem timeD_log_closed {n : ℕ} {O : Set (Space n)} {T : ℝ} (hT : 0 < T)
    {q : Point n → ℝ} {p : Point n} (hp : p ∈ O ×ˢ Ioc 0 T)
    (hqt : DifferentiableWithinAt ℝ (fun t => q (p.1,t)) (Icc 0 T) p.2)
    (hne : q p ≠ 0) :
    timeD (cylinder (closure O) 0 T) (fun z => Real.log (q z)) p =
      timeD (cylinder (closure O) 0 T) q p/q p := by
  have hf : {t | (p.1,t) ∈ cylinder (closure O) 0 T} = Icc 0 T := by
    ext t
    simp [cylinder, subset_closure hp.1]
  simp only [timeD, hf]
  exact (hqt.hasDerivWithinAt.log hne).derivWithin
    (uniqueDiffOn_Icc hT p.2 ⟨hp.2.1.le,hp.2.2⟩)

/-- The original divergence equation gives the actual logarithmic equation,
with principal matrix a/q and drift b/q. This holds also at the top face. -/
theorem expDivergence_log_equation {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    {T m : ℝ} (hT : 0 < T) (hm : 0 < m)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    {R q : Point n → ℝ}
    (ha : ContDiffOn ℝ ∞ a (cylinder (closure O) 0 T))
    (hq : C2 (cylinder (closure O) 0 T) q)
    (hbound : ∀ p ∈ cylinder (closure O) 0 T, m ≤ q p)
    (heq : ExpDivergenceEquation (O ×ˢ Ioc 0 T) a b R q) :
    ∀ p ∈ O ×ˢ Ioc 0 T,
      linearOp (cylinder (closure O) 0 T) (fun z => (q z)⁻¹ • a z)
        (fun z j => b z j/q z) (fun z => Real.log (q z)) p = (1-1/q p)*R p := by
  intro p hp
  have hpQ : p ∈ cylinder (closure O) 0 T :=
    ⟨subset_closure hp.1,hp.2.1.le,hp.2.2⟩
  have hne : q p ≠ 0 := (hm.trans_le (hbound p hpQ)).ne'
  have hqs : ∀ x ∈ O, ContDiffAt ℝ 2 (fun x => q (x,p.2)) x := by
    intro x hx
    exact hq.2.2.2.2.1 (x,p.2) ⟨subset_closure hx,hpQ.2⟩
  have hpos : ∀ x ∈ O, q (x,p.2) ≠ 0 := by
    intro x hx
    exact (hm.trans_le (hbound (x,p.2) ⟨subset_closure hx,hpQ.2⟩)).ne'
  have has : ContDiffOn ℝ ∞ (fun x => a (x,p.2)) O :=
    ha.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      (fun x hx => ⟨subset_closure hx,hpQ.2⟩)
  have had : ∀ i j, DifferentiableAt ℝ (fun x => a (x,p.2) i j) p.1 := by
    intro i j
    exact (L16Aux.matrixEntryCLM i j).differentiableAt.comp p.1
      ((has.contDiffAt (hO.mem_nhds hp.1)).differentiableAt (by simp))
  have hf := log_flux_divergence hO hp.1 had hqs hpos
  have hqt : DifferentiableWithinAt ℝ (fun t => q (p.1,t)) (Icc 0 T) p.2 := by
    have h := hq.2.2.2.2.2 p hpQ
    have hfiber : {t | (p.1,t) ∈ cylinder (closure O) 0 T} = Icc 0 T := by
      ext t
      simp [cylinder, hpQ.1]
    simpa only [hfiber] using h
  have htime := timeD_log_closed hT hp hqt hne
  have hgrad (j : Yau.RIdx n) :
      d (fun x => q (x,p.2)) p.1 j =
        q p*spatialD (fun z => Real.log (q z)) p (Yau.realVec j) := by
    have hh := d_log ((hqs p.1 hp.1).differentiableAt (by norm_num)) hne j
    change spatialD (fun z => Real.log (q z)) p (Yau.realVec j) =
      d (fun x => q (x,p.2)) p.1 j/q p at hh
    rw [hh]
    field_simp
  have hdiv :
      (∑ i, d (fun x => ∑ j, (a (x,p.2) i j/q (x,p.2))*
        d (fun y => q (y,p.2)) x j) p.1 i) =
      (∑ i, ∑ j, d (fun x => a (x,p.2) i j) p.1 i*
        spatialD (fun z => Real.log (q z)) p (Yau.realVec j)) +
      ∑ i, ∑ j, a p i j*spatialDD (fun z => Real.log (q z)) p (Yau.realVec i) (Yau.realVec j) := by
    simp only [hf, Finset.sum_add_distrib]
    rfl
  have hdrift : (∑ j, ((b p j-∑ i, d (fun x => a (x,p.2) i j) p.1 i)/q p)*
      d (fun x => q (x,p.2)) p.1 j) =
      (∑ j, b p j*spatialD (fun z => Real.log (q z)) p (Yau.realVec j)) -
      ∑ i, ∑ j, d (fun x => a (x,p.2) i j) p.1 i*
        spatialD (fun z => Real.log (q z)) p (Yau.realVec j) := by
    simp only [hgrad]
    have hc (j : Yau.RIdx n) :
        (b p j-∑ i, d (fun x => a (x,p.2) i j) p.1 i)/q p*
          (q p*spatialD (fun z => Real.log (q z)) p (Yau.realVec j)) =
        b p j*spatialD (fun z => Real.log (q z)) p (Yau.realVec j) -
          ∑ i, d (fun x => a (x,p.2) i j) p.1 i*
            spatialD (fun z => Real.log (q z)) p (Yau.realVec j) := by
      rw [← Finset.sum_mul]
      field_simp <;> ring
    simp only [hc, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
  have he := heq p hp
  rw [← timeD_closed_eq_halfOpen hp q, hdiv, hdrift] at he
  have hmain : timeD (cylinder (closure O) 0 T) q p -
      (∑ i, ∑ j, a p i j*spatialDD (fun z => Real.log (q z)) p (Yau.realVec i) (Yau.realVec j)) -
      (∑ j, b p j*spatialD (fun z => Real.log (q z)) p (Yau.realVec j)) = (q p-1)*R p := by
    linarith
  simp only [linearOp, htime, Matrix.smul_apply, smul_eq_mul]
  have hsumA : (∑ i, ∑ j, (q p)⁻¹*a p i j*
      spatialDD (fun z => Real.log (q z)) p (Yau.realVec i) (Yau.realVec j)) =
      (∑ i, ∑ j, a p i j*spatialDD (fun z => Real.log (q z)) p (Yau.realVec i) (Yau.realVec j))/q p := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hsumB : (∑ j, b p j/q p*spatialD (fun z => Real.log (q z)) p (Yau.realVec j)) =
      (∑ j, b p j*spatialD (fun z => Real.log (q z)) p (Yau.realVec j))/q p := by
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsumA, hsumB, ← sub_div, ← sub_div, hmain]
  field_simp <;> ring

end Yau.LeafProofs.L16ExpBoundaryAux
