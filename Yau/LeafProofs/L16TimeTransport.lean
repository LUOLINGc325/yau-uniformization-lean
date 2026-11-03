import Yau.LeafProofs.L16ShortInverse

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def timeTranslatePoint {n : ℕ} (τ : ℝ) (p : Point n) : Point n := (p.1,p.2+τ)

def timeTranslate {n : ℕ} {V : Type*} (τ : ℝ) (u : Point n → V) : Point n → V :=
  fun p => u (timeTranslatePoint τ p)

theorem timeTranslatePoint_mem_cylinder {n : ℕ} {l r τ : ℝ} {p : Point n}
    (hp : p ∈ cylinder Set.univ l r) :
    timeTranslatePoint τ p ∈ cylinder Set.univ (l+τ) (r+τ) :=
  ⟨Set.mem_univ _,add_le_add hp.2.1 le_rfl,add_le_add hp.2.2 le_rfl⟩

theorem timeTranslatePoint_contDiff {n : ℕ} (τ : ℝ) :
    ContDiff ℝ ∞ (timeTranslatePoint (n := n) τ) :=
  contDiff_fst.prodMk (contDiff_snd.add contDiff_const)

theorem timeTranslate_contDiffOn {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l r τ : ℝ} {u : Point n → V}
    (hu : ContDiffOn ℝ ∞ u (cylinder Set.univ (l+τ) (r+τ))) :
    ContDiffOn ℝ ∞ (timeTranslate τ u) (cylinder Set.univ l r) :=
  hu.comp (timeTranslatePoint_contDiff τ).contDiffOn
    (fun _ hp => timeTranslatePoint_mem_cylinder hp)

theorem holderBound_timeTranslate {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C l r τ : ℝ} {u : Point n → V}
    (hu : HolderBound α (cylinder Set.univ (l+τ) (r+τ)) u C) :
    HolderBound α (cylinder Set.univ l r) (timeTranslate τ u) C := by
  refine ⟨hu.1,fun p hp => hu.2.1 _ (timeTranslatePoint_mem_cylinder hp),?_⟩
  intro p hp q hq
  have h := hu.2.2 _ (timeTranslatePoint_mem_cylinder hp) _ (timeTranslatePoint_mem_cylinder hq)
  simpa only [timeTranslate,timeTranslatePoint,holderWeight,Prod.fst,Prod.snd,add_sub_add_right_eq_sub] using h

theorem spatialD_timeTranslate {n : ℕ} (τ : ℝ) (u : Point n → ℝ) (p : Point n) :
    spatialD (timeTranslate τ u) p = spatialD u (timeTranslatePoint τ p) := rfl

theorem spatialDD_timeTranslate {n : ℕ} (τ : ℝ) (u : Point n → ℝ) (p : Point n) :
    spatialDD (timeTranslate τ u) p = spatialDD u (timeTranslatePoint τ p) := rfl

theorem hasDerivWithinAt_timeTranslate {n : ℕ} {l r τ : ℝ} {u : Point n → ℝ}
    {p : Point n} (_hp : p ∈ cylinder Set.univ l r)
    (hu : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc (l+τ) (r+τ)) (p.2+τ)) :
    HasDerivWithinAt (fun t => timeTranslate τ u (p.1,t))
      (derivWithin (fun t => u (p.1,t)) (Set.Icc (l+τ) (r+τ)) (p.2+τ))
      (Set.Icc l r) p.2 := by
  have h := hu.hasDerivWithinAt.comp p.2 ((hasDerivAt_id p.2).add_const τ).hasDerivWithinAt
    (show Set.MapsTo (fun t : ℝ => t+τ) (Set.Icc l r) (Set.Icc (l+τ) (r+τ)) from
      fun t ht => ⟨add_le_add ht.1 le_rfl,add_le_add ht.2 le_rfl⟩)
  convert! h using 1
  simp only [mul_one]

theorem timeD_timeTranslate {n : ℕ} {l r τ : ℝ} (hlr : l < r) {u : Point n → ℝ}
    {p : Point n} (hp : p ∈ cylinder Set.univ l r)
    (hu : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc (l+τ) (r+τ)) (p.2+τ)) :
    timeD (cylinder Set.univ l r) (timeTranslate τ u) p =
      timeD (cylinder Set.univ (l+τ) (r+τ)) u (timeTranslatePoint τ p) := by
  have h := (hasDerivWithinAt_timeTranslate hp hu).derivWithin (uniqueDiffOn_Icc hlr _ hp.2)
  simpa only [timeD,timeTranslatePoint,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
    Set.mem_univ,true_and,Set.ofPred_mem_eq] using h

theorem c2_timeTranslate {n : ℕ} {l r τ : ℝ} (hlr : l < r) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ (l+τ) (r+τ)) u) :
    C2 (cylinder Set.univ l r) (timeTranslate τ u) := by
  let Q : Set (Point n) := cylinder Set.univ l r
  let Q' : Set (Point n) := cylinder Set.univ (l+τ) (r+τ)
  have hMap : Set.MapsTo (timeTranslatePoint τ) Q Q' := fun _ hp => timeTranslatePoint_mem_cylinder hp
  have hCont : ContinuousOn (timeTranslatePoint (n := n) τ) Q :=
    (timeTranslatePoint_contDiff τ).continuous.continuousOn
  have hU (p : Point n) (hp : p ∈ Q) :
      DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc (l+τ) (r+τ)) (p.2+τ) := by
    simpa only [timeTranslatePoint,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,Set.mem_univ,true_and,Set.ofPred_mem_eq]
      using hu.2.2.2.2.2 _ (hMap hp)
  refine ⟨hu.1.comp hCont hMap,hu.2.1.comp hCont hMap,
    hu.2.2.1.comp hCont hMap,?_,?_,?_⟩
  · apply (hu.2.2.2.1.comp hCont hMap).congr
    intro p hp
    exact timeD_timeTranslate hlr hp (hU p hp)
  · intro p hp
    exact hu.2.2.2.2.1 _ (hMap hp)
  · intro p hp
    simpa only [Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,Set.mem_univ,true_and,Set.ofPred_mem_eq]
      using (hasDerivWithinAt_timeTranslate hp (hU p hp)).differentiableWithinAt

theorem linearOp_timeTranslate {n : ℕ} {l r τ : ℝ} (hlr : l < r)
    {u : Point n → ℝ} (hu : C2 (cylinder Set.univ (l+τ) (r+τ)) u)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    {p : Point n} (hp : p ∈ cylinder Set.univ l r) :
    linearOp (cylinder Set.univ l r) (timeTranslate τ a) (timeTranslate τ b)
      (timeTranslate τ u) p =
      linearOp (cylinder Set.univ (l+τ) (r+τ)) a b u (timeTranslatePoint τ p) := by
  have hU : DifferentiableWithinAt ℝ (fun t => u (p.1,t))
      (Set.Icc (l+τ) (r+τ)) (p.2+τ) := by
    simpa only [timeTranslatePoint,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,Set.mem_univ,true_and,Set.ofPred_mem_eq]
      using hu.2.2.2.2.2 _ (timeTranslatePoint_mem_cylinder hp)
  simp only [linearOp,timeD_timeTranslate hlr hp hU,spatialD_timeTranslate,spatialDD_timeTranslate]
  rfl

theorem schauderBound_timeTranslate {n : ℕ} {α C l r τ : ℝ} (hlr : l < r)
    {u : Point n → ℝ} (hu : SchauderBound α (cylinder Set.univ (l+τ) (r+τ)) u C) :
    SchauderBound α (cylinder Set.univ l r) (timeTranslate τ u) C := by
  refine ⟨c2_timeTranslate hlr hu.1,hu.2.1,
    fun p hp => hu.2.2.1 _ (timeTranslatePoint_mem_cylinder hp),
    holderBound_timeTranslate hu.2.2.2.1,?_⟩
  apply holderBound_congr_on (holderBound_timeTranslate hu.2.2.2.2)
  intro p hp
  apply (timeD_timeTranslate hlr hp _).symm
  simpa only [timeTranslatePoint,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
    Set.mem_univ,true_and,Set.ofPred_mem_eq] using hu.1.2.2.2.2.2 _ (timeTranslatePoint_mem_cylinder hp)

theorem timeD_cylinder_restrict_time {n : ℕ} {l r L R : ℝ} (hlr : l < r)
    (hLl : L ≤ l) (hrR : r ≤ R) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ L R) u) {p : Point n}
    (hp : p ∈ cylinder Set.univ l r) :
    timeD (cylinder Set.univ l r) u p = timeD (cylinder Set.univ L R) u p := by
  have hp' : p ∈ cylinder Set.univ L R := ⟨Set.mem_univ _,hLl.trans hp.2.1,hp.2.2.trans hrR⟩
  have hU : DifferentiableWithinAt ℝ (fun t => u (p.1,t)) (Set.Icc L R) p.2 := by
    simpa only [Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
      Set.mem_univ,true_and,Set.ofPred_mem_eq] using hu.2.2.2.2.2 p hp'
  have h := (hU.hasDerivWithinAt.mono (Set.Icc_subset_Icc hLl hrR)).derivWithin
    (uniqueDiffOn_Icc hlr _ hp.2)
  simpa only [timeD,Yau.Parabolic.cylinder,Set.mem_ofPred_eq,Set.mem_prod,
    Set.mem_univ,true_and,Set.ofPred_mem_eq] using h

theorem c2_cylinder_restrict_time {n : ℕ} {l r L R : ℝ} (hlr : l < r)
    (hLl : L ≤ l) (hrR : r ≤ R) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ L R) u) : C2 (cylinder Set.univ l r) u := by
  have hSub : cylinder (n := n) Set.univ l r ⊆ cylinder Set.univ L R :=
    fun _ hp => ⟨Set.mem_univ _,hLl.trans hp.2.1,hp.2.2.trans hrR⟩
  refine ⟨hu.1.mono hSub,hu.2.1.mono hSub,hu.2.2.1.mono hSub,?_,
    fun p hp => hu.2.2.2.2.1 p (hSub hp),?_⟩
  · exact (hu.2.2.2.1.mono hSub).congr (fun p hp => timeD_cylinder_restrict_time hlr hLl hrR hu hp)
  · intro p hp
    exact (hu.2.2.2.2.2 p (hSub hp)).mono (fun t ht => hSub ht)

theorem linearOp_cylinder_restrict_time {n : ℕ} {l r L R : ℝ} (hlr : l < r)
    (hLl : L ≤ l) (hrR : r ≤ R) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ L R) u) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) {p : Point n} (hp : p ∈ cylinder Set.univ l r) :
    linearOp (cylinder Set.univ l r) a b u p = linearOp (cylinder Set.univ L R) a b u p := by
  simp only [linearOp,timeD_cylinder_restrict_time hlr hLl hrR hu hp]

theorem schauderBound_cylinder_restrict_time {n : ℕ} {α C l r L R : ℝ} (hlr : l < r)
    (hLl : L ≤ l) (hrR : r ≤ R) {u : Point n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ L R) u C) :
    SchauderBound α (cylinder Set.univ l r) u C := by
  have hSub : cylinder (n := n) Set.univ l r ⊆ cylinder Set.univ L R :=
    fun _ hp => ⟨Set.mem_univ _,hLl.trans hp.2.1,hp.2.2.trans hrR⟩
  refine ⟨c2_cylinder_restrict_time hlr hLl hrR hu.1,hu.2.1,
    fun p hp => hu.2.2.1 p (hSub hp),holderBound_mono hu.2.2.2.1 hSub,?_⟩
  exact holderBound_congr_on (holderBound_mono hu.2.2.2.2 hSub)
    (fun p hp => (timeD_cylinder_restrict_time hlr hLl hrR hu.1 hp).symm)

def spatialTraceLift {n : ℕ} {V : Type*} (τ : ℝ) (u : Point n → V) : Point n → V :=
  fun p => u (p.1,τ)

theorem spatialD_spatialTraceLift {n : ℕ} (τ : ℝ) (u : Point n → ℝ) (p : Point n) :
    spatialD (spatialTraceLift τ u) p = spatialD u (p.1,τ) := rfl

theorem spatialDD_spatialTraceLift {n : ℕ} (τ : ℝ) (u : Point n → ℝ) (p : Point n) :
    spatialDD (spatialTraceLift τ u) p = spatialDD u (p.1,τ) := rfl

theorem timeD_spatialTraceLift {n : ℕ} (Q : Set (Point n)) (τ : ℝ) (u : Point n → ℝ) :
    timeD Q (spatialTraceLift τ u) = 0 := by
  funext p
  simp only [timeD,spatialTraceLift,derivWithin_fun_const,Pi.zero_apply]

theorem c2_spatialTraceLift {n : ℕ} {l r τ : ℝ} {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ l r) u) (hτ : τ ∈ Set.Icc l r) (Q : Set (Point n)) :
    C2 Q (spatialTraceLift τ u) := by
  have hMap : Set.MapsTo (fun p : Point n => (p.1,τ)) Q (cylinder Set.univ l r) :=
    fun _ _ => ⟨Set.mem_univ _,hτ⟩
  have hCont : ContinuousOn (fun p : Point n => (p.1,τ)) Q :=
    (continuous_fst.prodMk continuous_const).continuousOn
  refine ⟨hu.1.comp hCont hMap,hu.2.1.comp hCont hMap,hu.2.2.1.comp hCont hMap,?_,?_,?_⟩
  · rw [timeD_spatialTraceLift]
    exact continuousOn_const
  · intro p hp
    exact hu.2.2.2.2.1 _ (hMap hp)
  · intro p hp
    exact differentiableWithinAt_const (u (p.1,τ))

theorem holderBound_spatialTraceLift {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C l r τ : ℝ} (hα : 0 < α) {u : Point n → V}
    (hu : HolderBound α (cylinder Set.univ l r) u C) (hτ : τ ∈ Set.Icc l r)
    (Q : Set (Point n)) : HolderBound α Q (spatialTraceLift τ u) C := by
  refine ⟨hu.1,fun p _ => hu.2.1 (p.1,τ) ⟨Set.mem_univ _,hτ⟩,?_⟩
  intro p hp q hq
  have h := hu.2.2 (p.1,τ) ⟨Set.mem_univ _,hτ⟩ (q.1,τ) ⟨Set.mem_univ _,hτ⟩
  have hExp : α/2 ≠ 0 := ne_of_gt (by positivity)
  simp only [holderWeight,sub_self,abs_zero,Real.zero_rpow hExp,add_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hu.1)

theorem schauderBound_spatialTraceLift {n : ℕ} {α C l r τ : ℝ} (hα : 0 < α)
    {u : Point n → ℝ} (hu : SchauderBound α (cylinder Set.univ l r) u C)
    (hτ : τ ∈ Set.Icc l r) (Q : Set (Point n)) : SchauderBound α Q (spatialTraceLift τ u) C := by
  refine ⟨c2_spatialTraceLift hu.1 hτ Q,hu.2.1,
    fun p _ => hu.2.2.1 (p.1,τ) ⟨Set.mem_univ _,hτ⟩,
    holderBound_spatialTraceLift hα hu.2.2.2.1 hτ Q,?_⟩
  rw [timeD_spatialTraceLift]
  exact holderBound_mono_const (holderBound_const α Q (0 : ℝ)) (by simpa using hu.2.1)

theorem timeTranslatePoint_sub {n : ℕ} (τ : ℝ) (p q : Point n) :
    timeTranslatePoint τ p-timeTranslatePoint τ q = p-q := by
  ext <;> simp only [timeTranslatePoint,Prod.fst_sub,Prod.snd_sub,add_sub_add_right_eq_sub]

theorem elliptic_timeTranslate {n : ℕ} {l r τ lam upper : ℝ} {a : Point n → Mat n}
    (ha : Elliptic (cylinder Set.univ (l+τ) (r+τ)) a lam upper) :
    Elliptic (cylinder Set.univ l r) (timeTranslate τ a) lam upper :=
  ⟨ha.1,ha.2.1,fun p hp => ha.2.2 _ (timeTranslatePoint_mem_cylinder hp)⟩

theorem smooth_coefficients_common_bounds {n : ℕ} {α T : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1) {K : Set (Space n)} (hK : IsCompact K)
    {a : Point n → Mat n} {b : Point n → Yau.RIdx n → ℝ}
    (hSmooth : SmoothCoefficients (cylinder Set.univ 0 T) a b)
    (hExterior : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, a (x,t) = 1 ∧ b (x,t) = 0) :
    ∃ M L : ℝ, 0 < M ∧ 0 < L ∧ HolderBound α (cylinder Set.univ 0 T) a M ∧
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) ∧
      ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T, ‖a p-a q‖ ≤ L*‖p-q‖ := by
  have haExt : ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T, a (x,t) = 1 :=
    fun x hx t ht => (hExterior x hx t ht).1
  obtain ⟨CA,hCA,hA⟩ := smooth_cylinder_compact_perturbation_holder hT hα hα1 hK hSmooth.1 haExt
  have hbEach (i : Yau.RIdx n) : ∃ C : ℝ, 0 < C ∧
      HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) C := by
    exact smooth_cylinder_compact_perturbation_holder hT hα hα1 hK (hSmooth.2 i)
      (c := (0 : ℝ)) (fun x hx t ht => by rw [(hExterior x hx t ht).2]; rfl)
  choose CB hCB hB using hbEach
  obtain ⟨L,hL,_,_,hLip⟩ := smooth_cylinder_compact_perturbation_bounds hT hK hSmooth.1 haExt
  let M : ℝ := 1+CA+∑ i : Yau.RIdx n, CB i
  have hSum : 0 ≤ ∑ i : Yau.RIdx n, CB i := Finset.sum_nonneg (fun i _ => (hCB i).le)
  have hM : 0 < M := by dsimp only [M]; linarith
  have hCA : CA ≤ M := by dsimp only [M]; linarith
  have hCBM (i : Yau.RIdx n) : CB i ≤ M := by
    have hBi := Finset.single_le_sum (s := Finset.univ) (f := CB)
      (fun j _ => (hCB j).le) (Finset.mem_univ i)
    dsimp only [M]
    linarith
  exact ⟨M,L,hM,hL,holderBound_mono_const hA hCA,
    fun i => holderBound_mono_const (hB i) (hCBM i),hLip⟩

theorem timeTranslatePoint_mem_subslab {n : ℕ} {T S τ : ℝ} (hτ : 0 ≤ τ) (hST : S+τ ≤ T)
    {p : Point n} (hp : p ∈ cylinder Set.univ 0 S) :
    timeTranslatePoint τ p ∈ cylinder Set.univ 0 T := by
  exact ⟨Set.mem_univ _,by dsimp only [timeTranslatePoint]; linarith [hp.2.1],
    (add_le_add hp.2.2 le_rfl).trans hST⟩

theorem holderBound_timeTranslate_subslab {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C T S τ : ℝ} (hτ : 0 ≤ τ) (hST : S+τ ≤ T) {u : Point n → V}
    (hu : HolderBound α (cylinder Set.univ 0 T) u C) :
    HolderBound α (cylinder Set.univ 0 S) (timeTranslate τ u) C := by
  apply holderBound_timeTranslate
  exact holderBound_mono hu (fun p hp => ⟨Set.mem_univ _,by linarith [hp.2.1],hp.2.2.trans hST⟩)

theorem contDiffOn_timeTranslate_subslab {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T S τ : ℝ}
    (hτ : 0 ≤ τ) (hST : S+τ ≤ T) {u : Point n → V}
    (hu : ContDiffOn ℝ ∞ u (cylinder Set.univ 0 T)) :
    ContDiffOn ℝ ∞ (timeTranslate τ u) (cylinder Set.univ 0 S) := by
  apply timeTranslate_contDiffOn
  exact hu.mono (fun p hp => ⟨Set.mem_univ _,by linarith [hp.2.1],hp.2.2.trans hST⟩)

theorem elliptic_timeTranslate_subslab {n : ℕ} {T S τ lam upper : ℝ}
    (hτ : 0 ≤ τ) (hST : S+τ ≤ T) {a : Point n → Mat n}
    (ha : Elliptic (cylinder Set.univ 0 T) a lam upper) :
    Elliptic (cylinder Set.univ 0 S) (timeTranslate τ a) lam upper :=
  ⟨ha.1,ha.2.1,fun _ hp => ha.2.2 _ (timeTranslatePoint_mem_subslab hτ hST hp)⟩

theorem lipschitz_timeTranslate_subslab {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {T S τ L : ℝ} (hτ : 0 ≤ τ) (hST : S+τ ≤ T) {u : Point n → V}
    (hu : ∀ p ∈ cylinder Set.univ 0 T, ∀ q ∈ cylinder Set.univ 0 T, ‖u p-u q‖ ≤ L*‖p-q‖) :
    ∀ p ∈ cylinder Set.univ 0 S, ∀ q ∈ cylinder Set.univ 0 S,
      ‖timeTranslate τ u p-timeTranslate τ u q‖ ≤ L*‖p-q‖ := by
  intro p hp q hq
  have h := hu _ (timeTranslatePoint_mem_subslab hτ hST hp) _ (timeTranslatePoint_mem_subslab hτ hST hq)
  simpa only [timeTranslate,timeTranslatePoint_sub] using h

theorem timeTranslate_cancel {n : ℕ} {V : Type*} (τ : ℝ) (u : Point n → V) :
    timeTranslate (-τ) (timeTranslate τ u) = u := by
  funext p
  simp only [timeTranslate,timeTranslatePoint,neg_add_cancel_right]

theorem c2_timeUntranslate {n : ℕ} {S τ : ℝ} (hS : 0 < S) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 S) u) :
    C2 (cylinder Set.univ τ (τ+S)) (timeTranslate (-τ) u) := by
  have h0 : τ+(-τ) = 0 := by ring
  have h1 : τ+S+(-τ) = S := by ring
  apply c2_timeTranslate (by linarith : τ < τ+S)
  simpa only [h0,h1] using hu

theorem schauderBound_timeUntranslate {n : ℕ} {α C S τ : ℝ} (hS : 0 < S) {u : Point n → ℝ}
    (hu : SchauderBound α (cylinder Set.univ 0 S) u C) :
    SchauderBound α (cylinder Set.univ τ (τ+S)) (timeTranslate (-τ) u) C := by
  have h0 : τ+(-τ) = 0 := by ring
  have h1 : τ+S+(-τ) = S := by ring
  apply schauderBound_timeTranslate (by linarith : τ < τ+S)
  simpa only [h0,h1] using hu

theorem holderBound_timeUntranslate {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    {α C S τ : ℝ} {u : Point n → V} (hu : HolderBound α (cylinder Set.univ 0 S) u C) :
    HolderBound α (cylinder Set.univ τ (τ+S)) (timeTranslate (-τ) u) C := by
  have h0 : τ+(-τ) = 0 := by ring
  have h1 : τ+S+(-τ) = S := by ring
  apply holderBound_timeTranslate
  simpa only [h0,h1] using hu

theorem linearOp_timeUntranslate {n : ℕ} {S τ : ℝ} (hS : 0 < S) {u : Point n → ℝ}
    (hu : C2 (cylinder Set.univ 0 S) u) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) {p : Point n}
    (hp : p ∈ cylinder Set.univ τ (τ+S)) :
    linearOp (cylinder Set.univ τ (τ+S)) (timeTranslate (-τ) a) (timeTranslate (-τ) b)
      (timeTranslate (-τ) u) p =
      linearOp (cylinder Set.univ 0 S) a b u (timeTranslatePoint (-τ) p) := by
  have h0 : τ+(-τ) = 0 := by ring
  have h1 : τ+S+(-τ) = S := by ring
  have hu' : C2 (cylinder Set.univ (τ+(-τ)) (τ+S+(-τ))) u := by
    simpa only [h0,h1] using hu
  simpa only [h0,h1] using linearOp_timeTranslate (τ := -τ) (by linarith : τ < τ+S) hu' a b hp

end Yau.LeafProofs.L16Aux
