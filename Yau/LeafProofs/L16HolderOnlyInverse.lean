import Yau.LeafProofs.L16HolderOnlyLocalization

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The genuine finite heat parametrix has a constant chosen before the
    frozen matrices, provided their heat norm factors have a common bound. -/
theorem finiteHeatParametrix_uniform_full_regularity {n : ℕ} {ι : Type*} {α N : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hN : 0 ≤ N) (s : Finset ι)
    (φ ψ : ι → Space n → ℝ) {E P : ℝ} (hE : 0 < E) (hP : 0 < P)
    (hφ : ∀ i ∈ s, ContDiff ℝ 2 (φ i))
    (hφ0 : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 1) (fun p => φ i p.1) E)
    (hφ1 : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (φ i) p.1) E)
    (hφ2 : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (fderiv ℝ (φ i)) p.1) E)
    (hψ : ∀ i ∈ s, HolderBound α (cylinder Set.univ 0 1) (fun p => ψ i p.1) P) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ι → Space n ≃L[ℝ] Space n,
      (∀ i ∈ s, constantHeatNormFactor α (B i) ≤ N) →
      ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (finiteHeatParametrix s B φ ψ f) (C*F) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (finiteHeatParametrix s B φ ψ f p,
          spatialD (finiteHeatParametrix s B φ ψ f) p)) (C*F) := by
  classical
  obtain ⟨CH,hCH,hHeat⟩ := constantHeatDuhamel_controlled_bounds (n := n) hα hα1
  let L : ℝ := 2*CH*(2*P)*N
  let W : ℝ := 8*E*L
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hSumW : 0 ≤ ∑ _i ∈ s, W := Finset.sum_nonneg (fun i _ => hW)
  refine ⟨1+∑ _i ∈ s, W,by linarith,?_⟩
  intro B hB T F hT hT1 f hf
  let Q := cylinder (n := n) Set.univ 0 T
  let v : ι → Point n → ℝ := fun i => constantHeatDuhamel (B i) (fun p => ψ i p.1*f p)
  have hSub : Q ⊆ cylinder Set.univ 0 1 := cylinder_mono_time hT1
  have hv (i : ι) (hi : i ∈ s) : C2 Q (v i) ∧
      HolderBound α Q (v i) (L*F) ∧
      HolderBound α Q (spatialD (v i)) (L*F) ∧
      HolderBound α Q (spatialDD (v i)) (L*F) ∧
      HolderBound α Q (timeD Q (v i)) (L*F) := by
    have hSource := holderBound_mul (holderBound_mono (hψ i hi) hSub) hf
    have hHeatI := hHeat N (B i) (hB i hi) T (2*P*F) hT hT1 _ hSource
    have hB0 : 0 ≤ CH*(2*P*F)*N := hHeatI.1.2.1
    have hMain : CH*(2*P*F)*N ≤ L*F := by dsimp only [L]; nlinarith
    have hPow1 : T^(1/2:ℝ) ≤ 1 := Real.rpow_le_one hT.le hT1 (by norm_num)
    have hPow2 : T^((1-α)/2) ≤ 1 := Real.rpow_le_one hT.le hT1 (by linarith)
    have hLowBound : CH*(2*P*F)*N*(T^(1/2:ℝ)+T^((1-α)/2)) ≤ L*F := by
      calc
        _ ≤ CH*(2*P*F)*N*2 := mul_le_mul_of_nonneg_left (by linarith) hB0
        _ = _ := by dsimp only [L]; ring
    have hLow := holderBound_mono_const hHeatI.2.2 hLowBound
    exact ⟨hHeatI.1.1,holderBound_fst hLow,holderBound_snd hLow,
      holderBound_mono_const hHeatI.1.2.2.2.1 hMain,
      holderBound_mono_const hHeatI.1.2.2.2.2 hMain⟩
  have hPatch (i : ι) (hi : i ∈ s) : C2 Q (fun p => φ i p.1*v i p) ∧
      HolderBound α Q (fun p => φ i p.1*v i p) (W*F) ∧
      HolderBound α Q (spatialD (fun p => φ i p.1*v i p)) (W*F) ∧
      HolderBound α Q (spatialDD (fun p => φ i p.1*v i p)) (W*F) ∧
      HolderBound α Q (timeD Q (fun p => φ i p.1*v i p)) (W*F) := by
    have hV := hv i hi
    have h := cutoff_full_jet_holderBound (hφ i hi) hV.1
      (holderBound_mono (hφ0 i hi) hSub) (holderBound_mono (hφ1 i hi) hSub)
      (holderBound_mono (hφ2 i hi) hSub) hV.2.1 hV.2.2.1 hV.2.2.2.1 hV.2.2.2.2
    simpa only [W,mul_assoc] using h
  have hSum := full_jet_finset_sum s hPatch
  have hBudget : (∑ _i ∈ s, W*F) ≤ (1+∑ _i ∈ s, W)*F := by
    rw [← Finset.sum_mul]
    nlinarith [hf.1]
  have h0 := holderBound_mono_const hSum.2.1 hBudget
  have h1 := holderBound_mono_const hSum.2.2.1 hBudget
  have h2 := holderBound_mono_const hSum.2.2.2.1 hBudget
  have ht := holderBound_mono_const hSum.2.2.2.2 hBudget
  change SchauderBound α Q (fun p => ∑ i ∈ s, φ i p.1*v i p) _ ∧ _
  refine ⟨⟨hSum.1,h0.1,?_,h2,ht⟩,?_⟩
  · intro p hp
    exact ⟨by simpa only [Real.norm_eq_abs] using h0.2.1 p hp,h1.2.1 p hp⟩
  · exact ⟨h0.1,fun p hp => max_le (h0.2.1 p hp) (h1.2.1 p hp),
      fun p hp q hq => max_le (h0.2.2 p hp q hq) (h1.2.2 p hp q hq)⟩

theorem localizedHeatParametrix_uniform_full_regularity {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (N : ℝ) (hN0 : 0 ≤ N) (s : Finset (Space n)) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n),
      (∀ c, constantHeatNormFactor α (B c) ≤ N) →
      constantHeatNormFactor α Bext ≤ N →
      ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (localizedHeatParametrix s hr B Bext f) (C*F) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (localizedHeatParametrix s hr B Bext f p,
          spatialD (localizedHeatParametrix s hr B Bext f) p)) (C*F) := by
  obtain ⟨Cφ,hCφ,hCut⟩ := patchBumps_uniform_three_holderBounds (n := n) hα hα1
  obtain ⟨E0,E1,E2,hE0,hE1,hE2,hExt0,hExt1,hExt2⟩ := exteriorCutoff_holder_jets hα hα1 s hr
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  let I0 := cutoffJetBudget α Cφ r 0
  let I1 := cutoffJetBudget α Cφ r 1
  let I2 := cutoffJetBudget α Cφ r 2
  have hI0 : 0 ≤ I0 := by dsimp only [I0,cutoffJetBudget]; positivity
  have hI1 : 0 ≤ I1 := by dsimp only [I1,cutoffJetBudget]; positivity
  have hI2 : 0 ≤ I2 := by dsimp only [I2,cutoffJetBudget]; positivity
  let E : ℝ := 1+I0+I1+I2+E0+E1+E2
  have hE : 0 < E := by dsimp only [E]; linarith
  have hIE0 : I0 ≤ E := by dsimp only [E]; linarith
  have hIE1 : I1 ≤ E := by dsimp only [E]; linarith
  have hIE2 : I2 ≤ E := by dsimp only [E]; linarith
  have hEE0 : E0 ≤ E := by dsimp only [E]; linarith
  have hEE1 : E1 ≤ E := by dsimp only [E]; linarith
  have hEE2 : E2 ≤ E := by dsimp only [E]; linarith
  have hφ0 (i : Option (Space n)) : HolderBound α (cylinder Set.univ 0 1)
      (fun p => localizationOuter s hr i p.1) E := by
    cases i with
    | none => exact holderBound_mono_const hExt0 hEE0
    | some c =>
      have h := (hCut r hr hr1 1 c _ (Or.inr rfl)).1
      apply holderBound_mono_const h
      simpa only [I0,cutoffJetBudget,Nat.zero_add,pow_one] using hIE0
  have hφ1 (i : Option (Space n)) : HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (localizationOuter s hr i) p.1) E := by
    cases i with
    | none => exact holderBound_mono_const hExt1 hEE1
    | some c =>
      exact holderBound_mono_const (hCut r hr hr1 1 c _ (Or.inr rfl)).2.1 hIE1
  have hφ2 (i : Option (Space n)) : HolderBound α (cylinder Set.univ 0 1)
      (fun p => fderiv ℝ (fderiv ℝ (localizationOuter s hr i)) p.1) E := by
    cases i with
    | none => exact holderBound_mono_const hExt2 hEE2
    | some c =>
      exact holderBound_mono_const (hCut r hr hr1 1 c _ (Or.inr rfl)).2.2 hIE2
  have hPS : 0 < P*r⁻¹*r^(1-α) := by positivity
  obtain ⟨C,hC,hUniform⟩ := finiteHeatParametrix_uniform_full_regularity
    (N := N) hα hα1 hN0 (localizationIndices s)
    (localizationOuter s hr) (localizationSource s hr) hE hPS
    (fun i _ => localizationOuter_contDiff s hr i) (fun i _ => hφ0 i)
    (fun i _ => hφ1 i) (fun i _ => hφ2 i) (fun i _ => hSource s r hr hr1 hSep 1 i)
  refine ⟨C,hC,?_⟩
  intro B Bext hB hBext
  apply hUniform (localizationEquiv B Bext)
  intro i hi
  cases i with
  | none => exact hBext
  | some c => exact hB c

theorem localizedHeatParametrix_weighted_inverse {n : ℕ} {α T : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hT : 0 < T) (hT1 : T ≤ 1)
    (s : Finset (Space n)) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hSep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → r ≤ ‖c-d‖)
    (B : Space n → Space n ≃L[ℝ] Space n) (Bext : Space n ≃L[ℝ] Space n)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (hGram : localizationGramIdentity s B Bext a)
    {β CP : ℝ} (hβ : 0 < β) (hCP : 0 < CP)
    (hWeighted : ∀ (f : Point n → ℝ) (F S : ℝ),
      HolderBound α (cylinder Set.univ 0 T) f F → 0 ≤ S → S ≤ F →
      (∀ p ∈ cylinder Set.univ 0 T, |f p| ≤ S) →
      HolderBound α (cylinder Set.univ 0 T)
        (localizedHeatResidual T s r hr B Bext a b f) (F/4+β*S/4) ∧
      (∀ p ∈ cylinder Set.univ 0 T,
        |localizedHeatResidual T s r hr B Bext a b f p| ≤ F/(4*β)))
    (hParametrix : ∀ (f : Point n → ℝ) (F : ℝ),
      HolderBound α (cylinder Set.univ 0 T) f F →
      SchauderBound α (cylinder Set.univ 0 T) (localizedHeatParametrix s hr B Bext f) (CP*F) ∧
      HolderBound α (cylinder Set.univ 0 T)
        (fun p => (localizedHeatParametrix s hr B Bext f p,
          spatialD (localizedHeatParametrix s hr B Bext f) p)) (CP*F)) :
    ∀ (f : Point n → ℝ) (F : ℝ), HolderBound α (cylinder Set.univ 0 T) f F →
      ∃ u : Point n → ℝ,
      SchauderBound α (cylinder Set.univ 0 T) u ((2*(1+β)*CP)*F) ∧
      HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) ((2*(1+β)*CP)*F) ∧
      (∀ x, u (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 T,
        linearOp (cylinder Set.univ 0 T) a b u p = f p := by
  let Q : Set (Point n) := cylinder Set.univ 0 T
  let : NormedAddCommGroup (holderGraph α Q) := inferInstance
  let : NormedSpace ℝ (holderGraph α Q) := inferInstance
  obtain ⟨P,hP,hSource⟩ := localizationSource_holderBound (n := n) hα hα1
  have hφ : ∀ i ∈ localizationIndices s, ContDiff ℝ 2 (localizationOuter s hr i) :=
    fun i _ => localizationOuter_contDiff s hr i
  have hψ : ∀ i ∈ localizationIndices s,
      HolderBound α Q (fun p => localizationSource s hr i p.1) (P*r⁻¹*r^(1-α)) :=
    fun i _ => hSource s r hr hr1 hSep T i
  let D : holderGraph α Q → Point n → ℝ := fun x =>
    finiteHeatResidual T (localizationIndices s) (localizationEquiv B Bext)
      (localizationOuter s hr) (localizationSource s hr) a b (holderGraphFun x)
  have hResidualEq {f : Point n → ℝ} {F : ℝ} (hf : HolderBound α Q f F)
      {p : Point n} (hp : p ∈ Q) :
      finiteHeatResidual T (localizationIndices s) (localizationEquiv B Bext)
        (localizationOuter s hr) (localizationSource s hr) a b f p =
        localizedHeatResidual T s r hr B Bext a b f p := by
    unfold finiteHeatResidual
    change linearOp Q a b (localizedHeatParametrix s hr B Bext f) p-f p = _
    rw [localizedHeatParametrix_linearOp hα hα1 hT hT1 s hr hr1 hSep B Bext a b hGram hf hp]
    ring
  have hProjection (x : holderGraph α Q) : ‖x.val.1‖ ≤ ‖x‖ := by
    change ‖x.val.1‖ ≤ max ‖x.val.1‖ ‖x.val.2‖
    exact le_max_left _ _
  have hGraphSup (x : holderGraph α Q) (p : Point n) (hp : p ∈ Q) :
      |holderGraphFun x p| ≤ ‖x.val.1‖ := by
    rw [holderGraphFun_apply x ⟨p,hp⟩]
    exact x.val.1.norm_coe_le_norm ⟨p,hp⟩
  have hRefined (x : holderGraph α Q) :
      HolderBound α Q (D x) (‖x‖/4+β*‖x.val.1‖/4) ∧
      (∀ p ∈ Q, |D x p| ≤ ‖x‖/(4*β)) := by
    have h := hWeighted (holderGraphFun x) ‖x‖ ‖x.val.1‖
      (holderGraphFun_holderBound x) (norm_nonneg _) (hProjection x) (hGraphSup x)
    refine ⟨holderBound_congr_on h.1 (fun p hp => (hResidualEq (holderGraphFun_holderBound x) hp).symm),?_⟩
    intro p hp
    rw [show D x p = localizedHeatResidual T s r hr B Bext a b (holderGraphFun x) p from
      hResidualEq (holderGraphFun_holderBound x) hp]
    exact h.2 p hp
  have hBound (x : holderGraph α Q) : HolderBound α Q (D x) (((1+β)/4)*‖x‖) := by
    apply holderBound_mono_const (hRefined x).1
    have h := mul_le_mul_of_nonneg_left (hProjection x) hβ.le
    nlinarith
  have hAdd (x y : holderGraph α Q) (p : Point n) (hp : p ∈ Q) :
      D (x+y) p = D x p+D y p := by
    dsimp only [D]
    rw [holderGraphFun_add]
    exact finiteHeatResidual_add _ _ _ _ a b hα hα1 hT hT1 hφ hψ
      (holderGraphFun_holderBound x) (holderGraphFun_holderBound y) hp
  have hSmul (c : ℝ) (x : holderGraph α Q) (p : Point n) (hp : p ∈ Q) :
      D (c • x) p = c*D x p := by
    dsimp only [D]
    rw [holderGraphFun_smul]
    exact finiteHeatResidual_smul _ _ _ _ a b hα hα1 hT hT1 hφ hψ
      (holderGraphFun_holderBound x) c hp
  let R : holderGraph α Q →L[ℝ] holderGraph α Q := holderGraphLift hα D hBound hAdd hSmul
  have hStrong (x : holderGraph α Q) :
      ‖R x‖ ≤ (1/4 : ℝ)*‖x‖+(β/4)*‖x.val.1‖ := by
    apply holderGraph_norm_le_of_holderBound (R x)
    have hHolder := holderBound_congr_on (hRefined x).1 (show
      Set.EqOn (D x) (holderGraphFun (R x)) Q from by
      intro p hp
      rw [holderGraphFun_apply (R x) ⟨p,hp⟩]
      rfl)
    convert hHolder using 1; ring
  have hSupR (x : holderGraph α Q) :
      ‖(R x).val.1‖ ≤ (1/(4*β))*‖x‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro p
    change |D x p.val| ≤ _
    convert (hRefined x).2 p.val p.property using 1; ring
  have hεd : (1/4 : ℝ)+β*(1/(4*β)) ≤ (1/2 : ℝ) := by
    have hCancel : β*(1/(4*β)) = (1/4 : ℝ) := by field_simp [hβ.ne']
    rw [hCancel]
    norm_num
  have hAB : β/4 ≤ β/2 := by linarith
  intro f F hf
  let fH : holderGraph α Q := holderGraphOfBound hα hf
  obtain ⟨g,hCorrect,hg⟩ := holderGraph_residual_correction_of_two_bounds R hβ.le hεd hAB hStrong hSupR fH
  let u : Point n → ℝ := localizedHeatParametrix s hr B Bext (holderGraphFun g)
  have hBudget : CP*‖g‖ ≤ (2*(1+β)*CP)*F := by
    have hgf : ‖g‖ ≤ 2*(1+β)*F := hg.trans
      (mul_le_mul_of_nonneg_left (holderGraphOfBound_norm_le hα hf) (by positivity))
    nlinarith
  have hU := hParametrix (holderGraphFun g) ‖g‖ (holderGraphFun_holderBound g)
  refine ⟨u,schauderBound_mono_const hU.1 hBudget,
    holderBound_mono_const hU.2 hBudget,localizedHeatParametrix_initial s hr B Bext (holderGraphFun g),?_⟩
  intro p hp
  have hEval := congrArg (fun x : holderGraph α Q => x.val.1 ⟨p,hp⟩) hCorrect
  have hPoint : holderGraphFun g p+D g p = f p := by
    rw [holderGraphFun_apply g ⟨p,hp⟩]
    change g.val.1 ⟨p,hp⟩+(R g).val.1 ⟨p,hp⟩ = f p
    exact hEval
  change linearOp Q a b (localizedHeatParametrix s hr B Bext (holderGraphFun g)) p = f p
  rw [localizedHeatParametrix_linearOp hα hα1 hT hT1 s hr hr1 hSep B Bext a b hGram
    (holderGraphFun_holderBound g) hp]
  rw [← hResidualEq (holderGraphFun_holderBound g) hp]
  exact hPoint



/-- A genuinely uniform short inverse with only Holder coefficient bounds.
    Both the time scale and solution constant precede every coefficient family. -/
theorem exists_uniform_short_schauder_inverse_holder_only {n : ℕ}
    {α M lam upper : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      0 < T → T ≤ δ → HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      Elliptic (cylinder Set.univ 0 T) a lam upper →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      ∀ (f : Point n → ℝ) (F : ℝ),
        HolderBound α (cylinder Set.univ 0 T) f F → ∃ u : Point n → ℝ,
        SchauderBound α (cylinder Set.univ 0 T) u (C*F) ∧
        HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) (C*F) ∧
        (∀ x, u (x,0) = 0) ∧ ∀ p ∈ cylinder Set.univ 0 T,
          linearOp (cylinder Set.univ 0 T) a b u p = f p := by
  let N : ℝ := ellipticHeatNormBudget α lam upper
  have hN : 0 ≤ N := by dsimp only [N,ellipticHeatNormBudget]; positivity
  obtain ⟨r,hr,s,β,δ,hr1,hsK,hSep,hCover,hβ,hδ,hδ1,hWeighted⟩ :=
    exists_localizedHeatResidual_holder_only_weighted_bounds
      (n := n) (M := M) (N := N) hα hα1 hK
  obtain ⟨CP,hCP,hParametrix⟩ :=
    localizedHeatParametrix_uniform_full_regularity hα hα1 N hN s hr hr1 hSep
  refine ⟨δ,2*(1+β)*CP,hδ,hδ1,by positivity,?_⟩
  intro T a b hT hTδ ha hb hEll hExterior
  obtain ⟨B,hBN,hNid,hGram⟩ := elliptic_localization_equivs hα.le hT.le a hEll s
  exact localizedHeatParametrix_weighted_inverse hα hα1 hT (hTδ.trans hδ1) s hr hr1 hSep
    B (ContinuousLinearEquiv.refl ℝ (Space n)) a b hGram hβ hCP
    (fun f F S hf hS hSF hSup => hWeighted T a b B
      (ContinuousLinearEquiv.refl ℝ (Space n)) f F S hT hTδ
      ha hb hExterior hBN hNid hf hS hSF hSup)
    (fun f F hf => hParametrix B (ContinuousLinearEquiv.refl ℝ (Space n))
      hBN hNid T F hT (hTδ.trans hδ1) f hf)

end Yau.LeafProofs.L16Aux
