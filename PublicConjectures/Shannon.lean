import PublicConjectures.Incidence

noncomputable section
namespace Shannon
open Real

abbrev Pt := ℝ × ℝ
def vertex (n : ℕ) (i : ℤ) : Pt := (cos ((i:ℝ)*angle n), sin ((i:ℝ)*angle n))
def lerp (s : ℝ) (p q : Pt) : Pt := ((1-s)*p.1+s*q.1, (1-s)*p.2+s*q.2)

/-- t runs through 1/(k+1),...,k/(k+1). On the incoming side it is measured
backwards from the corner, and on the outgoing side the forward fraction is 1-t. -/
@[ext] structure Edge (n k : ℕ) where
  corner : Fin n
  t : ℚ
  pos : 0 < t
  lt_one : t < 1
  grid : ∃ j : Fin k, t = (j.val+1:ℚ)/(k+1)

def point (e : Edge n k) (s : ℝ) : Pt :=
  let i : ℤ := e.corner.val
  lerp s (lerp e.t (vertex n i) (vertex n (i-1)))
    (lerp (1-e.t) (vertex n i) (vertex n (i+1)))

def OnEdge (p : Pt) (e : Edge n k) : Prop := ∃ s : ℝ, 0 < s ∧ s < 1 ∧ p = point e s

def TripleCross (n k : ℕ) : Prop :=
  ∃ (p : Pt) (a b d : Edge n k), a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
    OnEdge p a ∧ OnEdge p b ∧ OnEdge p d

private def xf (e : Edge n k) (s : ℝ) := s*(1-(e.t:ℝ))
private def yf (e : Edge n k) (s : ℝ) := (1-s)*(e.t:ℝ)
private def view (e : Edge n k) (s : ℝ) := frame n e.corner.val (xf e s) (yf e s)

private theorem project (e : Edge n k) (s φ : ℝ) :
    view e s φ = (point e s).1 * cos φ + (point e s).2 * sin φ := by
  unfold view frame point lerp vertex xf yf V
  simp only [cos_sub]; ring

private theorem view_eq {a b : Edge n k} {s t : ℝ} :
    point a s = point b t ↔ view a s = view b t := by
  constructor
  · intro h; funext φ; rw [project,project,h]
  · intro h
    apply Prod.ext
    · simpa only [project,cos_zero,sin_zero,mul_one,mul_zero,add_zero] using congrFun h 0
    · simpa only [project,cos_pi_div_two,sin_pi_div_two,mul_one,mul_zero,zero_add] using congrFun h (π/2)

private theorem interior (e : Edge n k) {s : ℝ} (h : 0 < s) (h' : s < 1) :
    0 ≤ xf e s ∧ 0 ≤ yf e s ∧ xf e s + yf e s < 1 := by
  have hp : (0:ℝ) < e.t := by exact_mod_cast e.pos
  have hq : (e.t:ℝ) < 1 := by exact_mod_cast e.lt_one
  unfold xf yf
  refine ⟨mul_nonneg h.le (sub_nonneg.mpr hq.le), mul_nonneg (sub_nonneg.mpr h'.le) hp.le, ?_⟩
  nlinarith [mul_pos h hp, mul_pos (sub_pos.mpr h') (sub_pos.mpr hq)]

private theorem touching {n k : ℕ} (hn : 3 ≤ n) {a b : Edge n k} {s t : ℝ}
    (hs : 0 < s) (hs' : s < 1) (ht : 0 < t) (ht' : t < 1) (h : view a s = view b t) :
    Near n a.corner.val b.corner.val := by
  obtain ⟨_,_,H⟩ := interior a hs hs'
  obtain ⟨h1,h2,h3⟩ := interior b ht ht'
  apply near_of_inter hn (by positivity) (by exact_mod_cast a.corner.isLt)
    (by positivity) (by exact_mod_cast b.corner.isLt) H h1 h2 h3.le h

private def Side (n : ℕ) (i j : ℤ) : Prop := j=i ∨ j=i+1 ∨ j+(n:ℤ)=i+1

private theorem commonSide {n : ℕ} (hn : 5 ≤ n) {a b d : Fin n}
    (h : Near n a.val b.val) (g : Near n a.val d.val) (f : Near n b.val d.val) :
    ∃ i : ℤ, Side n i a.val ∧ Side n i b.val ∧ Side n i d.val := by
  have ha := a.isLt; have hb := b.isLt; have hd := d.isLt
  have : (Side n a.val b.val ∧ Side n a.val d.val) ∨
      (Side n b.val a.val ∧ Side n b.val d.val) ∨
      (Side n d.val a.val ∧ Side n d.val b.val) := by
    unfold Near at *; unfold Side; omega
  rcases this with h | h | h
  · exact ⟨a.val, Or.inl rfl,h⟩
  · exact ⟨b.val,h.1,Or.inl rfl,h.2⟩
  · exact ⟨d.val,h.1,h.2,Or.inl rfl⟩

private def label (i : ℤ) (e : Edge n k) : Bool × ℚ :=
  if (e.corner.val:ℤ) = i then (false,e.t) else (true,1-e.t)

private theorem label_ne_zero (i : ℤ) (e : Edge n k) : (label i e).2 ≠ 0 := by
  unfold label; split
  · exact e.pos.ne'
  · exact (sub_pos.mpr e.lt_one).ne'

private theorem label_inj {i : ℤ} {a b : Edge n k}
    (ha : Side n i a.corner.val) (hb : Side n i b.corner.val) :
    label i a = label i b → a = b := by
  intro h
  have h₁ := a.corner.isLt; have h₂ := b.corner.isLt
  unfold label at h
  unfold Side at ha hb
  split at h <;> split at h <;> simp at h
  all_goals apply Edge.ext
  all_goals first | exact h | apply Fin.ext; omega

private theorem rightView {i : ℤ} {e : Edge n k} (hn : 0 < n)
    (hs : Side n i e.corner.val) (ne : (e.corner.val:ℤ) ≠ i) (s : ℝ) :
    view e s = frame n i (1+2*cos (angle n)*xf e s-yf e s) (xf e s) := by
  unfold view
  have h := hs.resolve_left ne
  rw [← frame_next]
  rcases h with h | h
  · rw [h]
  · rw [← frame_period n hn (e.corner.val:ℤ), h]

private theorem coords {i : ℤ} {e : Edge n k} (hn : 0 < n)
    (hs : Side n i e.corner.val) (s : ℝ) : ∃ X Y, view e s = frame n i X Y := by
  by_cases h : (e.corner.val:ℤ) = i
  · exact ⟨xf e s,yf e s, by simp only [view,h]⟩
  · exact ⟨_,_,rightView hn hs h s⟩

private theorem fit {i : ℤ} {e : Edge n k} (hn : 3 ≤ n)
    (hs : Side n i e.corner.val) (s : ℝ) {X Y : ℝ}
    (eq : view e s = frame n i X Y) : Fits (cos (angle n)) X Y (label i e) := by
  by_cases h : (e.corner.val:ℤ) = i
  · simp only [view,h] at eq
    obtain ⟨rfl,rfl⟩ := frame_inj hn eq
    simp only [label,if_pos h,Fits,Bool.false_eq_true,if_false, Rel,xf,yf]
    have he : (e.t:ℝ) ≠ 0 := by exact_mod_cast e.pos.ne'
    field_simp; ring
  · rw [rightView (by omega) hs h] at eq
    obtain ⟨rfl,rfl⟩ := frame_inj hn eq
    simp only [label,if_neg h,Fits,if_true,Rel,xf,yf]
    push_cast
    have he : 1-(e.t:ℝ) ≠ 0 := by exact_mod_cast (sub_pos.mpr e.lt_one).ne'
    field_simp; ring

/-- Necessity for three pairwise distinct open segments on the actual regular polygon. -/
theorem only_exceptional (n k : ℕ) (hn : 3 ≤ n) (multi : TripleCross n k) :
    n=3 ∨ n=4 ∨ n=6 := by
  by_cases small : n < 5
  · omega
  obtain ⟨p,a,b,d,hab,had,hbd,⟨s,hs,hs',pa⟩,⟨t,ht,ht',pb⟩,u,hu,hu',pd⟩ := multi
  have ab := view_eq.mp (pa.symm.trans pb)
  have ad := view_eq.mp (pa.symm.trans pd)
  have bd := view_eq.mp (pb.symm.trans pd)
  obtain ⟨i,sa,sb,sd⟩ := commonSide (by omega : 5 ≤ n)
    (touching hn hs hs' ht ht' ab) (touching hn hs hs' hu hu' ad) (touching hn ht ht' hu hu' bd)
  obtain ⟨X,Y,hxy⟩ := coords (by omega : 0 < n) sa s
  apply exceptional_of_rat hn
  exact rational_of_triple (label_ne_zero i a) (label_ne_zero i b) (label_ne_zero i d)
    (fun h => hab (label_inj sa sb h)) (fun h => had (label_inj sa sd h))
    (fun h => hbd (label_inj sb sd h)) (fit hn sa s hxy) (fit hn sb t (ab.symm.trans hxy))
    (fit hn sd u (ad.symm.trans hxy))

private def gridEdge {n k : ℕ} (i : Fin n) (j : Fin k) : Edge n k where
  corner := i
  t := (j.val+1:ℚ)/(k+1)
  pos := by positivity
  lt_one := by
    apply (div_lt_one (by positivity : (0:ℚ) < k+1)).2
    exact_mod_cast Nat.add_lt_add_right j.isLt 1
  grid := ⟨j,rfl⟩

private theorem witness {n k : ℕ} (a b d : Edge n k) (s t u : ℚ)
    (ha : a.corner.val = 0) (hb : b.corner.val = 0) (hd : d.corner.val = 1)
    (ij : a.t ≠ b.t) (hs : 0 < s ∧ s < 1) (ht : 0 < t ∧ t < 1) (hu : 0 < u ∧ u < 1)
    (hab : xf a s = xf b t ∧ yf a s = yf b t)
    (had : xf a s = 1+2*cos (angle n)*xf d u-yf d u ∧ yf a s = xf d u) :
    TripleCross n k := by
  refine ⟨point a s,a,b,d, ?_,?_,?_,⟨s,by exact_mod_cast hs.1,by exact_mod_cast hs.2,rfl⟩,
    ⟨t,by exact_mod_cast ht.1,by exact_mod_cast ht.2,view_eq.mpr ?_⟩,
    ⟨u,by exact_mod_cast hu.1,by exact_mod_cast hu.2,view_eq.mpr ?_⟩⟩
  · exact fun eq => ij (congrArg Edge.t eq)
  · intro eq; rw [eq,hd] at ha; contradiction
  · intro eq; rw [eq,hd] at hb; contradiction
  · simp only [view,ha,hb,hab.1,hab.2]
  · simp only [view,ha,hd,Nat.cast_zero,Nat.cast_one,had.1,had.2]
    exact (frame_next n 0 _ _).symm

theorem triangle : TripleCross 3 5 := by
  have hc : cos (angle 3) = -1/2 := by
    rw [show angle 3 = π-π/3 by unfold angle; norm_num; ring, cos_pi_sub, cos_pi_div_three]
    ring
  apply witness (gridEdge ⟨0,by decide⟩ ⟨0,by decide⟩)
    (gridEdge ⟨0,by decide⟩ ⟨2,by decide⟩) (gridEdge ⟨1,by decide⟩ ⟨3,by decide⟩) (1/2) (5/6) (1/4)
  all_goals norm_num [xf,yf,gridEdge,hc]

theorem square : TripleCross 4 5 := by
  have hc : cos (angle 4) = 0 := by
    rw [show angle 4 = π/2 by unfold angle; norm_num; ring, cos_pi_div_two]
  apply witness (gridEdge ⟨0,by decide⟩ ⟨0,by decide⟩)
    (gridEdge ⟨0,by decide⟩ ⟨1,by decide⟩) (gridEdge ⟨1,by decide⟩ ⟨2,by decide⟩) (2/3) (5/6) (1/9)
  all_goals norm_num [xf,yf,gridEdge,hc]

theorem hexagon : TripleCross 6 9 := by
  have hc : cos (angle 6) = 1/2 := by
    rw [show angle 6 = π/3 by unfold angle; norm_num; ring, cos_pi_div_three]
  apply witness (gridEdge ⟨0,by decide⟩ ⟨0,by decide⟩)
    (gridEdge ⟨0,by decide⟩ ⟨4,by decide⟩) (gridEdge ⟨1,by decide⟩ ⟨7,by decide⟩) (1/2) (9/10) (1/4)
  all_goals norm_num [xf,yf,gridEdge,hc]

/-- Shannon's public conjecture, in both directions, with positive k witnesses. -/
theorem classification (n : ℕ) (hn : 3 ≤ n) :
    (∃ k : ℕ, TripleCross n k) ↔ n=3 ∨ n=4 ∨ n=6 := by
  constructor
  · rintro ⟨k,h⟩; exact only_exceptional n k hn h
  · rintro (rfl | rfl | rfl)
    · exact ⟨5,triangle⟩
    · exact ⟨5,square⟩
    · exact ⟨9,hexagon⟩

end Shannon
