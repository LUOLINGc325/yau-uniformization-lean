import Yau.LeafProofs.L16GlobalInverse

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- A Hölder directional derivative gives a uniform first-order
remainder estimate, with no extension outside the spatial slice. -/
theorem holder_directional_taylor_remainder {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) {g : E → V}
    (hg : ∀ x, DifferentiableAt ℝ g x) (e : E)
    (hHolder : ∀ x y, ‖fderiv ℝ g x e-fderiv ℝ g y e‖ ≤ C*‖x-y‖^α)
    (x : E) (h : ℝ) :
    ‖g (x+h • e)-g x-h • fderiv ℝ g x e‖ ≤ |h| *C*‖h • e‖^α := by
  let H : E := h • e
  let F : ℝ → V := fun t => g (x+t • H)-t • (h • fderiv ℝ g x e)
  let D : ℝ → V := fun t => h • (fderiv ℝ g (x+t • H) e-fderiv ℝ g x e)
  have hDeriv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivWithinAt F (D t) (Set.Icc (0 : ℝ) 1) t := by
    have hLine : HasDerivAt (fun s : ℝ => x+s • H) H t := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const H).const_add x
    have hG := (hg (x+t • H)).hasFDerivAt.comp_hasDerivAt t hLine
    have hF := (hG.sub ((hasDerivAt_id t).smul_const (h • fderiv ℝ g x e))).hasDerivWithinAt
      (s := Set.Icc (0 : ℝ) 1)
    convert! hF using 1
    simp only [D,H,one_smul,ContinuousLinearMap.map_smul,smul_sub]
  have hBound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖D t‖ ≤ |h| *C*‖H‖^α := by
    have hDist : ‖(x+t • H)-x‖ ≤ ‖H‖ := by
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
    calc
      ‖D t‖ = |h| *‖fderiv ℝ g (x+t • H) e-fderiv ℝ g x e‖ := by
        simp only [D,norm_smul,Real.norm_eq_abs]
      _ ≤ |h| *(C*‖(x+t • H)-x‖^α) :=
        mul_le_mul_of_nonneg_left (hHolder _ _) (abs_nonneg h)
      _ ≤ |h| *(C*‖H‖^α) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hDist hα) hC) (abs_nonneg h)
      _ = _ := by ring
  have hMV := norm_image_sub_le_of_norm_deriv_le_segment_01' hDeriv hBound
  convert hMV using 1
  · dsimp only [F,H]
    simp only [one_smul,zero_smul,add_zero,sub_zero]
    congr 1
    abel

theorem holder_directional_difference_quotient {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) {g : E → V}
    (hg : ∀ x, DifferentiableAt ℝ g x) (e : E)
    (hHolder : ∀ x y, ‖fderiv ℝ g x e-fderiv ℝ g y e‖ ≤ C*‖x-y‖^α)
    (x : E) {h : ℝ} (hh : h ≠ 0) :
    ‖h⁻¹ • (g (x+h • e)-g x)-fderiv ℝ g x e‖ ≤ C*‖h • e‖^α := by
  have hEq : h⁻¹ • (g (x+h • e)-g x)-fderiv ℝ g x e =
      h⁻¹ • (g (x+h • e)-g x-h • fderiv ℝ g x e) := by
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ hh,one_smul]
  rw [hEq,norm_smul,Real.norm_eq_abs,abs_inv]
  have h := mul_le_mul_of_nonneg_left (holder_directional_taylor_remainder hα hC hg e hHolder x h)
    (inv_nonneg.mpr (abs_nonneg h))
  convert h using 1
  field_simp

theorem spatial_difference_quotient_bound {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {α C T : ℝ}
    (hα : 0 < α) {g : Point n → V} (e : Space n)
    (hDiff : ∀ p ∈ cylinder Set.univ 0 T, DifferentiableAt ℝ (fun x => g (x,p.2)) p.1)
    (hHolder : HolderBound α (cylinder Set.univ 0 T) (spatialPartial g e) C)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 T) {h : ℝ} (hh : h ≠ 0) :
    ‖h⁻¹ • (g (p.1+h • e,p.2)-g p)-spatialPartial g e p‖ ≤ C*‖h • e‖^α := by
  change ‖h⁻¹ • (g (p.1+h • e,p.2)-g (p.1,p.2))-
    fderiv ℝ (fun x => g (x,p.2)) p.1 e‖ ≤ C*‖h • e‖^α
  apply holder_directional_difference_quotient (g := fun x => g (x,p.2)) hα.le hHolder.1
    (fun x => hDiff (x,p.2) ⟨Set.mem_univ _,hp.2⟩) e _ p.1 hh
  intro x y
  have h := hHolder.2.2 (x,p.2) ⟨Set.mem_univ _,hp.2⟩ (y,p.2) ⟨Set.mem_univ _,hp.2⟩
  simpa only [spatialPartial,holderWeight,sub_self,abs_zero,Real.zero_rpow (ne_of_gt (by positivity : 0 < α/2)),add_zero]
    using h

theorem derivative_eq_of_power_approximation {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {α C : ℝ} (hα : 0 < α)
    {f : ℝ → V} {d z : V} (hf : HasDerivAt f d 0)
    (hError : ∀ h : ℝ, 0 < h → ‖h⁻¹ • (f h-f 0)-z‖ ≤ C*h^α) : d = z := by
  let q : ℝ → V := fun h => h⁻¹ • (f h-f 0)
  have hPow : Tendsto (fun h : ℝ => C*h^α) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun h : ℝ => C*h^α) := continuous_const.mul (Real.continuous_rpow_const hα.le)
    have h := hc.tendsto 0
    have h0 := h.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa only [Real.zero_rpow hα.ne',mul_zero] using h0
  have hNorm : Tendsto (fun h => ‖q h-z‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hPow
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact hError h hh
  have hz : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 z) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hNorm
  have hd : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    simpa only [zero_add] using hf.tendsto_slope_zero_right
  exact tendsto_nhds_unique hd hz

def spatialDifferenceQuotient {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (u : Point n → V) (e : Space n) (h : ℝ) (p : Point n) : V :=
  h⁻¹ • (u (p.1+h • e,p.2)-u p)

/-- Supremum stability identifies a derivative from uniformly small
equation errors, without convergence in the full Hölder norm. -/
theorem spatialPartial_eq_of_residual_approximation {n : ℕ} {α T lam upper M U Z K : ℝ}
    (hα : 0 < α) (hT : 0 < T) (hM : 0 ≤ M) (hK : 0 ≤ K)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {u z : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 T) u) (hz : C2 (cylinder Set.univ 0 T) z)
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    (hb : ∀ p ∈ cylinder Set.univ 0 T, ∀ i, |b p i| ≤ M)
    (hU : ∀ p ∈ cylinder Set.univ 0 T, |u p| ≤ U)
    (hZ : ∀ p ∈ cylinder Set.univ 0 T, |z p| ≤ Z)
    (hInitU : ∀ x, u (x,0) = 0) (hInitZ : ∀ x, z (x,0) = 0) (e : Space n)
    (hQuotient : ∀ h : ℝ, 0 < h → C2 (cylinder Set.univ 0 T) (spatialDifferenceQuotient u e h))
    (hResidual : ∀ h : ℝ, 0 < h → ∀ p ∈ Set.univ ×ˢ Set.Ioc 0 T,
      |linearOp (cylinder Set.univ 0 T) a b (spatialDifferenceQuotient u e h) p-
        linearOp (cylinder Set.univ 0 T) a b z p| ≤ K*‖h • e‖^α) :
    Set.EqOn (spatialPartial u e) z (cylinder Set.univ 0 T) := by
  intro p hp
  have hLine : HasDerivAt (fun h : ℝ => p.1+h • e) e 0 := by
    simpa only [one_smul,id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add p.1
  have hDeriv := ((hu.2.2.2.2.1 p hp).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hLine (by simp)
  have hDeriv' : HasDerivAt (fun h : ℝ => u (p.1+h • e,p.2)) (spatialPartial u e p) 0 := by
    simpa only [Function.comp_def,zero_smul,add_zero,spatialPartial] using hDeriv
  apply derivative_eq_of_power_approximation (C := T*K*‖e‖^α) hα hDeriv'
  intro h hh
  have hq := hQuotient h hh
  have hBound (q : Point n) (hqmem : q ∈ cylinder Set.univ 0 T) :
      |spatialDifferenceQuotient u e h q-z q| ≤ |h⁻¹| *(U+U)+Z := by
    have hShift : (q.1+h • e,q.2) ∈ cylinder Set.univ 0 T := ⟨Set.mem_univ _,hqmem.2⟩
    calc
      _ ≤ |spatialDifferenceQuotient u e h q|+|z q| := abs_sub _ _
      _ = |h⁻¹| *|u (q.1+h • e,q.2)-u q|+|z q| := by
        simp only [spatialDifferenceQuotient,smul_eq_mul,abs_mul]
      _ ≤ |h⁻¹| *(|u (q.1+h • e,q.2)|+|u q|)+|z q| :=
        add_le_add (mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)) le_rfl
      _ ≤ |h⁻¹| *(U+U)+Z :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add (hU _ hShift) (hU q hqmem)) (abs_nonneg _)) (hZ q hqmem)
  have hInit (x : Space n) : spatialDifferenceQuotient u e h (x,0)-z (x,0) = 0 := by
    simp only [spatialDifferenceQuotient,hInitU,hInitZ,sub_self,smul_zero]
  have hOp (q : Point n) (hqmem : q ∈ Set.univ ×ˢ Set.Ioc 0 T) :
      |linearOp (cylinder Set.univ 0 T) a b (fun q => spatialDifferenceQuotient u e h q-z q) q| ≤ K*‖h • e‖^α := by
    rw [linearOp_sub hq hz ⟨Set.mem_univ _,hqmem.2.1.le,hqmem.2.2⟩]
    exact hResidual h hh q hqmem
  have hEstimate := bounded_wholeSpace_residual_bound hT (c2_sub hq hz) hEll hM hb hBound hInit
    (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)) hOp p hp
  have hTime : |spatialDifferenceQuotient u e h p-z p| ≤ T*(K*‖h • e‖^α) :=
    hEstimate.trans (mul_le_mul_of_nonneg_right hp.2.2 (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)))
  have hScale : T*(K*‖h • e‖^α) = (T*K*‖e‖^α)*h^α := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hh,Real.mul_rpow hh.le (norm_nonneg _)]
    ring
  simpa only [spatialDifferenceQuotient,Real.norm_eq_abs,zero_smul,add_zero,hScale] using hTime

theorem holderBound_spatial_increment {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C T : ℝ} (hα : 0 < α) {g : Point n → V}
    (hg : HolderBound α (cylinder Set.univ 0 T) g C) {p : Point n}
    (hp : p ∈ cylinder Set.univ 0 T) (v : Space n) :
    ‖g (p.1+v,p.2)-g p‖ ≤ C*‖v‖^α := by
  have h := hg.2.2 (p.1+v,p.2) ⟨Set.mem_univ _,hp.2⟩ p hp
  simpa only [holderWeight,add_sub_cancel_left,sub_self,abs_zero,
    Real.zero_rpow (ne_of_gt (by positivity : 0 < α/2)),add_zero] using h

theorem cylinder_spatialSlice_contDiff {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T t : ℝ} {g : Point n → V}
    (hg : ContDiffOn ℝ ∞ g (cylinder Set.univ 0 T)) (ht : t ∈ Set.Icc 0 T) :
    ContDiff ℝ ∞ (fun x : Space n => g (x,t)) := by
  have hEmbed : ContDiff ℝ ∞ (fun x : Space n => (x,t)) := contDiff_id.prodMk contDiff_const
  have h := hg.comp (s := Set.univ) hEmbed.contDiffOn (fun x _ => ⟨Set.mem_univ _,ht⟩)
  simpa only [Function.comp_def,contDiffOn_univ] using h

end Yau.LeafProofs.L16Aux
