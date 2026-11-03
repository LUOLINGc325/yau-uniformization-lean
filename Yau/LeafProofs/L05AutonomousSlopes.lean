import Yau.LeafProofs.L05DualEllipticity
import Yau.LeafProofs.L05JetCombinationMatrix
import Yau.LeafProofs.L16
import Mathlib.Analysis.LocallyConvex.Separation

noncomputable section
open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux Yau.ParabolicCandidates

local instance autoSlopesSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

def autoTraceFunctional {n : ℕ} (H : Sym n) : Sym n →L[ℝ] ℝ :=
  ∑ i, ∑ j, (H : Mat n) j i • symEntry n i j

theorem autoTraceFunctional_apply {n : ℕ} (H A : Sym n) :
    autoTraceFunctional H A=tracePair A H := by
  simp only [autoTraceFunctional,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,
    tracePair,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (H : Mat n) j i*(A : Mat n) i j=(A : Mat n) i j*(H : Mat n) j i
  ring

/-- A finite, globally defined continuous concave function has a genuine supporting
linear functional at zero. The separating vertical coefficient is proved strictly positive. -/
theorem auto_supporting_linear {n : ℕ} {F : Sym n → ℝ}
    (hF : Continuous F) (hC : ConcaveOn ℝ univ F) (h0 : F 0=0) :
    ∃ l : Sym n →L[ℝ] ℝ, ∀ H, F H≤l H := by
  let A : Set (Sym n × ℝ) := {p | p.2≤F p.1}
  have hA : Convex ℝ A := by
    simpa only [A,mem_univ,true_and] using hC.convex_hypograph
  have hstrict : IsOpen {p : Sym n × ℝ | p.2<F p.1} :=
    isOpen_lt continuous_snd (hF.comp continuous_fst)
  have hAint : (interior A).Nonempty := by
    refine ⟨(0,-1),?_⟩
    have hsub : {p : Sym n × ℝ | p.2<F p.1}⊆A := by
      intro p hp
      change p.2≤F p.1
      exact hp.le
    have hmem : ((0,-1) : Sym n × ℝ)∈{p | p.2<F p.1} := by
      change (-1:ℝ)<F 0
      rw [h0]
      norm_num
    exact interior_maximal hsub hstrict hmem
  have hnot : ((0,0) : Sym n × ℝ)∉interior A := by
    intro hx
    have hnhds : A∈𝓝 ((0,0) : Sym n × ℝ) :=
      Filter.mem_of_superset (isOpen_interior.mem_nhds hx) interior_subset
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnhds
    have hpoint : ((0,r/2) : Sym n × ℝ)∈Metric.ball (0,0) r := by
      simp only [Metric.mem_ball,Prod.dist_eq,dist_self,Real.dist_eq,sub_zero,
        abs_of_pos (by positivity : 0<r/2),max_lt_iff]
      exact ⟨hr,by linarith only [hr]⟩
    have hh := hball hpoint
    change r/2≤F 0 at hh
    rw [h0] at hh
    linarith only [hh,hr]
  obtain ⟨f,hfne,hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point hA hnot hAint
  let l : Sym n →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Sym n) ℝ)
  let k : ℝ := f (0,1)
  have hsplit (H : Sym n) (t : ℝ) : f (H,t)=l H+k*t := by
    have hadd := f.map_add (H,0) (0,t)
    simp only [Prod.mk_add_mk,add_zero,zero_add] at hadd
    have hmul := f.map_smul t ((0,1) : Sym n × ℝ)
    simp only [Prod.smul_mk,smul_zero,smul_eq_mul,mul_one] at hmul
    change f (0,t)=t*k at hmul
    rw [hadd,hmul]
    change f (H,0)+t*k=f (H,0)+k*t
    ring
  have hsep' (H : Sym n) (t : ℝ) (ht : t≤F H) : l H+k*t≤0 := by
    have hh := hsep (H,t) ht
    rw [hsplit] at hh
    change l H+k*t≤f 0 at hh
    simpa only [map_zero] using hh
  have hk0 : 0≤k := by
    have hh := hsep' 0 (-1) (by rw [h0]; norm_num)
    rw [map_zero] at hh
    linarith only [hh]
  have hk : 0<k := by
    by_contra hk
    have hkz : k=0 := le_antisymm (le_of_not_gt hk) hk0
    have hl (H : Sym n) : l H≤0 := by
      simpa only [hkz,zero_mul,add_zero] using hsep' H (F H) le_rfl
    have hlz (H : Sym n) : l H=0 := by
      have hh := hl (-H)
      rw [map_neg] at hh
      linarith only [hl H,hh]
    apply hfne
    apply ContinuousLinearMap.ext
    intro p
    rcases p with ⟨H,t⟩
    rw [hsplit,hlz,hkz]
    simp only [zero_mul,add_zero,ContinuousLinearMap.zero_apply]
  let support : Sym n →L[ℝ] ℝ := (-k⁻¹) • l
  refine ⟨support,?_⟩
  intro H
  have hh := hsep' H (F H) le_rfl
  change F H≤(-k⁻¹)*l H
  apply (mul_le_mul_iff_right₀ hk).mp
  have heq : k*((-k⁻¹)*l H) = -l H := by
    rw [← mul_assoc,mul_neg,mul_inv_cancel₀ hk.ne']
    ring
  rw [heq]
  linarith only [hh]

/-- The actual supporting matrix lies in the ellipticity interval; no DF is present. -/
theorem auto_supporting_slope {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0<ell) (hL : ell≤L) (hF : Continuous F)
    (hE : globalElliptic F ell L) (hC : ConcaveOn ℝ univ F) (h0 : F 0=0) :
    ∃ A ∈ slopeSet n ell L, ∀ H, F H≤tracePair A H := by
  obtain ⟨l,hl⟩ := auto_supporting_linear hF hC h0
  refine ⟨dualMatrix l.toLinearMap,dualMatrix_mem_slopeSet _ ?_,?_⟩
  · intro v
    have hlow := (hE 0 (rankOne v) (rankOne_posSemidef v)).1
    have hupp := (hE (-rankOne v) (rankOne v) (rankOne_posSemidef v)).2
    rw [zero_add,h0,sub_zero,rankOne_trace] at hlow
    rw [neg_add_cancel,h0,rankOne_trace] at hupp
    have hp := hl (rankOne v)
    have hm := hl (-rankOne v)
    rw [map_neg] at hm
    change ell*(∑ i, (v i)^2)≤l (rankOne v) ∧ l (rankOne v)≤L*(∑ i, (v i)^2)
    exact ⟨hlow.trans hp,by linarith only [hm,hupp]⟩
  intro H
  rw [← dualMatrix_apply]
  exact hl H

/-- Every nonlinear secant is an actual elliptic linear trace, without differentiating F. -/
theorem auto_secant_slope {n : ℕ} {ell L : ℝ} {F : Sym n → ℝ}
    (hell : 0<ell) (hL : ell≤L) (hE : globalElliptic F ell L) (H K : Sym n) :
    ∃ A ∈ slopeSet n ell L, F H-F K=tracePair A (H-K) := by
  let D := H-K
  let f := autoTraceFunctional D
  have hc := slopeSet_isCompact n (L := L) hell.le
  have hn := slopeSet_nonempty n hL
  obtain ⟨Amax,hAmax,hmax⟩ := hc.exists_isMaxOn hn f.continuous.continuousOn
  obtain ⟨Amin,hAmin,hmin⟩ := hc.exists_isMinOn hn f.continuous.continuousOn
  have hupper : F H-F K≤f Amax := by
    apply (jet_elliptic_difference_le_pucci hell.le hL hE H K).trans
    apply pucciPlus_le hL
    intro A hA
    rw [← autoTraceFunctional_apply]
    exact hmax hA
  have hneg : pucciPlus ell L (K-H)≤-f Amin := by
    apply pucciPlus_le hL
    intro A hA
    have hh := hmin hA
    change f Amin≤f A at hh
    have heq : tracePair A (K-H) = -f A := by
      dsimp only [f,D]
      rw [autoTraceFunctional_apply]
      simp only [tracePair,AddSubgroup.coe_sub,Matrix.mul_sub,Matrix.trace_sub]
      ring
    rw [heq]
    linarith only [hh]
  have hlower : f Amin≤F H-F K := by
    have hh := (jet_elliptic_difference_le_pucci hell.le hL hE K H).trans hneg
    linarith only [hh]
  have horder : f Amin≤f Amax := hmin hAmax
  by_cases heq : f Amax=f Amin
  · refine ⟨Amin,hAmin,?_⟩
    rw [← autoTraceFunctional_apply]
    exact le_antisymm (by simpa only [heq] using hupper) hlower
  have hgap : 0<f Amax-f Amin := sub_pos.mpr (lt_of_le_of_ne horder (Ne.symm heq))
  let theta := (F H-F K-f Amin)/(f Amax-f Amin)
  have ht : theta∈Icc 0 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hlower) hgap.le
    · exact (div_le_one hgap).mpr (by linarith only [hupper])
  have hA : (1-theta) • Amin+theta • Amax∈slopeSet n ell L :=
    (slopeSet_convex n ell L) hAmin hAmax (by linarith only [ht.2]) ht.1 (by ring)
  refine ⟨(1-theta) • Amin+theta • Amax,hA,?_⟩
  rw [← autoTraceFunctional_apply]
  change F H-F K=f ((1-theta) • Amin+theta • Amax)
  rw [map_add,map_smul,map_smul]
  change F H-F K=(1-theta)*f Amin+theta*f Amax
  dsimp only [theta]
  field_simp <;> ring

theorem auto_slope_quadratic_bounds {n : ℕ} {ell L : ℝ} {A : Sym n}
    (hA : A∈slopeSet n ell L) (v : Yau.RIdx n → ℝ) :
    ell*(∑ i, (v i)^2)≤∑ i, ∑ j, (A : Mat n) i j*v i*v j ∧
      (∑ i, ∑ j, (A : Mat n) i j*v i*v j)≤L*(∑ i, (v i)^2) := by
  have hh := slopeSet_tracePair_bounds hA (rankOne_posSemidef v)
  rw [rankOne_trace,tracePair_rankOne] at hh
  simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
    Finset.mul_sum,mul_left_comm,mul_assoc] using hh

/-- The actual symmetric square-root coordinate change, with the sharp ellipticity
operator budgets, obtained from the already proved constant-matrix construction. -/
theorem auto_slope_space_equiv {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    {A : Sym n} (hA : A∈slopeSet n ell L) :
    ∃ S : Space n ≃L[ℝ] Space n,
      ‖(S : Space n →L[ℝ] Space n)‖≤Real.sqrt L ∧
      ‖(S.symm : Space n →L[ℝ] Space n)‖≤(Real.sqrt ell)⁻¹ ∧
      ∀ B : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, B (S (Yau.realVec k)) (S (Yau.realVec k)))=
          ∑ i, ∑ j, (A : Mat n) i j*B (Yau.realVec i) (Yau.realVec j) := by
  have hsymm : (A : Mat n).IsSymm :=
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr A.property).isSymm
  exact L16Aux.elliptic_matrix_space_equiv (A : Mat n) hell hL hsymm
    (auto_slope_quadratic_bounds hA)

end Yau.LeafProofs.L05AutonomousAux
