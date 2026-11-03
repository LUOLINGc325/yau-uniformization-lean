import Yau.LeafProofs.L16Continuation
import Yau.LeafProofs.L16TimeGluing

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- Finite continuation of the genuine short inverse yields a bounded
classical inverse on every finite closed slab. -/
theorem bounded_holder_global_classical_solution {n : ℕ} {α T M L F lam upper : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hL : 0 ≤ L)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    (ha : HolderBound α (cylinder Set.univ 0 T) a M)
    (hb : ∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M)
    (hf : HolderBound α (cylinder Set.univ 0 T) f F)
    (hLip : ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T, ‖a p-a q‖ ≤ L*‖p-q‖)
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    {K : Set (Space n)} (hK : IsCompact K)
    (hExterior : ∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) :
    ∃ (u : Point n → ℝ) (D : ℝ), SchauderBound α (cylinder Set.univ 0 T) u D ∧
      HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) D ∧
      (∀ x, u (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 T,
        linearOp (cylinder Set.univ 0 T) a b u p = f p := by
  obtain ⟨δ,hδ,hδ1,hShort⟩ := exists_uniform_short_schauder_inverse
    (n := n) (M := M) (lam := lam) (upper := upper) hα hα1 hL hK
  obtain ⟨N,hNgt⟩ := exists_nat_gt (T/δ)
  have hNp : 0 < (N : ℝ) := (div_pos hT hδ).trans hNgt
  have hN : 0 < N := by exact_mod_cast hNp
  have hN1 : 1 ≤ N := hN
  let h : ℝ := T/(N : ℝ)
  have hh : 0 < h := div_pos hT hNp
  have hNh : (N : ℝ)*h = T := by dsimp only [h]; field_simp
  have hhδ : h ≤ δ := by
    dsimp only [h]
    apply (div_le_iff₀ hNp).mpr
    exact ((div_lt_iff₀ hδ).mp hNgt).le.trans_eq (mul_comm _ _)
  have hTimeLe (k : ℕ) (hk : k ≤ N) : (k : ℝ)*h ≤ T :=
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hh.le).trans_eq hNh
  let P : ℕ → Prop := fun k => ∃ (u : Point n → ℝ) (D : ℝ),
    SchauderBound α (cylinder Set.univ 0 ((k : ℝ)*h)) u D ∧
    HolderBound α (cylinder Set.univ 0 ((k : ℝ)*h)) (fun p => (u p,spatialD u p)) D ∧
    (∀ x, u (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 ((k : ℝ)*h),
      linearOp (cylinder Set.univ 0 ((k : ℝ)*h)) a b u p = f p
  have hBase : P 1 := by
    have hSub : cylinder (n := n) Set.univ 0 h ⊆ cylinder Set.univ 0 T :=
      cylinder_mono_time (by simpa only [Nat.cast_one,one_mul] using hTimeLe 1 hN1)
    obtain ⟨C,hC,hSolve⟩ := hShort h a b hh hhδ (holderBound_mono ha hSub)
      (fun i => holderBound_mono (hb i) hSub)
      (fun p hp q hq => hLip p (hSub hp) q (hSub hq)) (elliptic_mono hEll hSub)
      (fun p hp hx => hExterior p (hSub hp) hx)
    obtain ⟨u,hu,hLow,h0,hOp⟩ := hSolve f F (holderBound_mono hf hSub)
    exact ⟨u,C*F,by simpa only [Nat.cast_one,one_mul] using hu,
      by simpa only [Nat.cast_one,one_mul] using hLow,h0,
      by simpa only [Nat.cast_one,one_mul] using hOp⟩
  have hInd : ∀ k : ℕ, 1 ≤ k → k ≤ N → P k := by
    intro k hk1
    induction k,hk1 using Nat.le_induction with
    | base => intro _; exact hBase
    | succ k hk1 ih =>
      intro hkN
      have hkN' : k ≤ N := (Nat.le_succ k).trans hkN
      obtain ⟨u,C,hu,hLow,h0,hOp⟩ := ih hkN'
      let τ : ℝ := (k : ℝ)*h
      have hτ : 0 < τ := mul_pos (by exact_mod_cast hk1) hh
      have hEnd : h+τ ≤ T := by
        have hE := hTimeLe (k+1) hkN
        simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm,τ] using hE
      have haS := holderBound_timeTranslate_subslab hτ.le hEnd ha
      have hbS (i : Yau.RIdx n) := holderBound_timeTranslate_subslab hτ.le hEnd (hb i)
      have hLipS := lipschitz_timeTranslate_subslab hτ.le hEnd hLip
      have hEllS := elliptic_timeTranslate_subslab hτ.le hEnd hEll
      have hExtS (p : Point n) (hp : p ∈ cylinder Set.univ 0 h) (hx : p.1 ∉ K) :
          timeTranslate τ a p = 1 :=
        hExterior _ (timeTranslatePoint_mem_subslab hτ.le hEnd hp) hx
      obtain ⟨CS,hCS,hSolve⟩ := hShort h (timeTranslate τ a) (timeTranslate τ b) hh hhδ
        haS hbS hLipS hEllS hExtS
      obtain ⟨v,D,hv,hvLow,hv0,hvOp⟩ := short_inverse_with_trace_on_next_slab
        hα hh hτ.le hEnd hu hLow ha hb hf hSolve
      have hTrace (x : Space n) : u (x,τ) = v (x,τ) := (hv0 x).symm
      have htTrace (x : Space n) : timeD (cylinder Set.univ 0 τ) u (x,τ) =
          timeD (cylinder Set.univ τ (τ+h)) v (x,τ) := by
        apply timeD_eq_of_trace_and_operator a b hTrace x
        rw [hOp (x,τ) ⟨Set.mem_univ _,hτ.le,le_rfl⟩,
          hvOp (x,τ) ⟨Set.mem_univ _,le_rfl,by linarith⟩]
      have hPaste := timePaste_solution hα hτ (by linarith : τ < τ+h)
        hu hv hLow hvLow hTrace htTrace hOp hvOp
      have hPaste0 (x : Space n) : timePaste τ u v (x,0) = 0 :=
        (hPaste.2.2.1 ⟨Set.mem_univ _,le_rfl,hτ.le⟩).trans (h0 x)
      have hTime : τ+h = ((k+1 : ℕ) : ℝ)*h := by
        dsimp only [τ]
        push_cast
        ring
      refine ⟨timePaste τ u v,2*(C+D),?_,?_,hPaste0,?_⟩
      · simpa only [hTime] using hPaste.1
      · simpa only [hTime] using hPaste.2.1
      · simpa only [hTime] using hPaste.2.2.2.2
  obtain ⟨u,D,hu,hLow,h0,hOp⟩ := hInd N hN1 le_rfl
  exact ⟨u,D,by simpa only [hNh] using hu,by simpa only [hNh] using hLow,h0,
    by simpa only [hNh] using hOp⟩

theorem smooth_compact_global_classical_solution {n : ℕ} {α T lam upper : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ} {f : Point n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder Set.univ 0 T) a b)
    (hfSmooth : ContDiffOn ℝ ∞ f (cylinder Set.univ 0 T))
    (hEll : Elliptic (cylinder Set.univ 0 T) a lam upper)
    {K : Set (Space n)} (hK : IsCompact K)
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T,
      a (x,t) = 1 ∧ b (x,t) = 0 ∧ f (x,t) = 0) :
    ∃ (u : Point n → ℝ) (D : ℝ), SchauderBound α (cylinder Set.univ 0 T) u D ∧
      HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) D ∧
      (∀ x, u (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 T,
        linearOp (cylinder Set.univ 0 T) a b u p = f p := by
  obtain ⟨M,L,hM,hL,ha,hb,hLip⟩ := smooth_coefficients_common_bounds hT hα hα1 hK hSmooth
    (fun x hx t ht => ⟨(hExterior x hx t ht).1,(hExterior x hx t ht).2.1⟩)
  obtain ⟨F,hF,hf⟩ := smooth_cylinder_compact_perturbation_holder hT hα hα1 hK hfSmooth
    (fun x hx t ht => (hExterior x hx t ht).2.2)
  exact bounded_holder_global_classical_solution hα hα1 hT hL.le ha hb hf hLip hEll hK
    (fun p hp hx => (hExterior p.1 hx p.2 hp.2).1)

end Yau.LeafProofs.L16Aux
