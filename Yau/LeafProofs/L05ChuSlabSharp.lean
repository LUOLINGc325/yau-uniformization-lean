import Yau.LeafProofs.L05ChuTimeOscillation

noncomputable section

open Filter
open scoped Topology ContDiff

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic L16Aux

local instance l05ChuSlabSharpDualGroup (n : ℕ) : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuSlabSharpDualSpace (n : ℕ) : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance l05ChuSlabSharpHessianGroup (n : ℕ) : NormedAddCommGroup (DiniHessian n) := inferInstance
local instance l05ChuSlabSharpHessianSpace (n : ℕ) : NormedSpace ℝ (DiniHessian n) := inferInstance

theorem constant_causal_slab_sharp_oscillation (n : ℕ) (hn : 0 < n) (ell L : ℝ)
    (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Mat n) (l r eta gamma G F W MH epsilon A : ℝ) (g w : Point n → ℝ),
      l < r → r-l ≤ 1 → 0 < eta → eta < 1 → 0 < gamma → gamma < 1 →
      0 ≤ G → 0 ≤ F → 0 ≤ W → 0 ≤ epsilon → 0 ≤ A →
      Elliptic (cylinder Set.univ l r) (fun _ => a) ell L →
      HolderBound eta (cylinder Set.univ l r) g F →
      (∀ p ∈ cylinder Set.univ l r, |g p| ≤ G) → (∀ x : Space n, g (x,l)=0) →
      C2 (cylinder Set.univ l r) w → (∀ p ∈ cylinder Set.univ l r, |w p| ≤ W) →
      (∀ x : Space n, w (x,l)=0) →
      (∀ p ∈ Set.univ ×ˢ Set.Ioc l r,
        linearOp (cylinder Set.univ l r) (fun _ => a) (fun _ _ => 0) w p=g p) →
      HolderBound eta (cylinder Set.univ l r) (spatialDD w) MH →
      (∀ p ∈ cylinder Set.univ l r, ∀ q ∈ cylinder Set.univ l r,
        |g p-g q| ≤ epsilon*‖spatialDD w p-spatialDD w q‖+A*holderWeight gamma p q) →
      (C*epsilon)*diniPowerConstant gamma ≤ 1/2 → (C*epsilon)*diniPowerConstant eta ≤ 1/2 →
      powerBound gamma (2*(C*((2*A)*diniPowerConstant gamma+G)))
        (chuOscillation (cylinder Set.univ l r) (spatialDD w)) := by
  obtain ⟨C,hC,hSharp⟩ := constant_causal_sharp_oscillation n hn ell L hell hL
  refine ⟨C,hC,?_⟩
  intro a l r eta gamma G F W MH epsilon A g w hlr hT1 he he1 hg hg1 hG0 hF hW heps hA
    hEll hgf hG hg0 hw hwB hw0 hPDE hH hpair hSmallGamma hSmallEta
  let Q : Set (Point n) := cylinder Set.univ 0 (r-l)
  have hMap {p : Point n} (hp : p ∈ Q) : timeTranslatePoint l p ∈ cylinder Set.univ l r :=
    ⟨Set.mem_univ _,by change l ≤ p.2+l; linarith only [hp.2.1],by change p.2+l ≤ r; linarith only [hp.2.2]⟩
  have hShift {V : Type} [NormedAddCommGroup V] {f : Point n → V} {M : ℝ}
      (hf : HolderBound eta (cylinder Set.univ l r) f M) : HolderBound eta Q (timeTranslate l f) M := by
    have hh : HolderBound eta (cylinder Set.univ ((0:ℝ)+l) ((r-l)+l)) f M := by
      simpa only [zero_add,sub_add_cancel] using hf
    exact holderBound_timeTranslate_on_space hh
  have hEllShift : Elliptic Q (fun _ => a) ell L :=
    ⟨hEll.1,hEll.2.1,fun p hp => hEll.2.2 _ (hMap hp)⟩
  have hHShift : HolderBound eta Q (spatialDD (timeTranslate l w)) MH := by
    convert! hShift hH using 1
  have hPairShift (p : Point n) (hp : p ∈ Q) (q : Point n) (hq : q ∈ Q) :
      |timeTranslate l g p-timeTranslate l g q| ≤
        epsilon*‖spatialDD (timeTranslate l w) p-spatialDD (timeTranslate l w) q‖+A*holderWeight gamma p q := by
    rw [spatialDD_timeTranslate,spatialDD_timeTranslate]
    simpa only [timeTranslate,holderWeight,timeTranslatePoint,add_sub_add_right_eq_sub] using
      hpair _ (hMap hp) _ (hMap hq)
  have hPDEshift (p : Point n) (hp : p ∈ Set.univ ×ˢ Set.Ioc (0:ℝ) (r-l)) :
      linearOp Q (fun _ => a) (fun _ _ => 0) (timeTranslate l w) p=timeTranslate l g p := by
    rw [chu_constant_linearOp_timeTranslate_zero hlr a hw ⟨Set.mem_univ _,hp.2.1.le,hp.2.2⟩]
    apply hPDE
    exact ⟨Set.mem_univ _,by change l < p.2+l; linarith only [hp.2.1],by change p.2+l ≤ r; linarith only [hp.2.2]⟩
  have hResult := hSharp a (r-l) eta gamma G F W MH epsilon A (timeTranslate l g) (timeTranslate l w)
    (sub_pos.mpr hlr) hT1 he he1 hg hg1 hG0 hF hW heps hA hEllShift (hShift hgf)
    (fun p hp => hG _ (hMap hp)) (fun x => by simpa only [timeTranslate,timeTranslatePoint,zero_add] using hg0 x)
    (chu_c2_timeTranslate_slab_zero hlr hw) (fun p hp => hwB _ (hMap hp))
    (fun x => by simpa only [timeTranslate,timeTranslatePoint,zero_add] using hw0 x)
    hPDEshift hHShift hPairShift hSmallGamma hSmallEta
  have hOsc : chuOscillation Q (spatialDD (timeTranslate l w))=
      chuOscillation (cylinder Set.univ l r) (spatialDD w) := by
    have hFn : spatialDD (timeTranslate l w)=timeTranslate l (spatialDD w) := funext (spatialDD_timeTranslate l w)
    rw [hFn]
    change chuOscillation (cylinder Set.univ 0 (r-l)) (timeTranslate l (spatialDD w))=_
    rw [chuOscillation_timeTranslate,sub_add_cancel]
  rw [hOsc] at hResult
  exact hResult

end Yau.LeafProofs.L05Aux
